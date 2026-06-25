module resources/inventory_item/inventory_item

open meta/kernel                  // Entity/Scoped, EntityId, resolve, refs
open meta/values                  // Quantity (byUnit), PhysicalLocator, Unit
open meta/algebra/keyed_order     // classify/Sign, semanticEq/EqVerdict, lte; (→ keyed_monoid: isZero, add, negate, zero, Scalar, SZero)
open reference_data/item/item     // Item — the primary classifier

/*
 * InventoryItem (v1) — a discrete, homogeneous, non-overlapping amount of goods/materials
 * under a tenant's control, classified by an Item.
 *
 * TEMPORAL model (Phase B, DT-001.03 / DT-004): we model the single EFFECTIVE timeline
 * (Alloy 6 `var` + trace). Identity fields are immutable (constant across the trace) so an
 * InventoryItem keeps its identity through every operation; the MUTABLE state fields are `var`.
 * Membership of `Live` is the existence axis: Create adds, Delete/WriteOff/Merge-absorb remove.
 * Operations (the transition predicates that drive these fields) live in `operations.als`;
 * the rationale for modeling one effective timeline (and deferring recorded-time/bitemporal
 * replay) is workbook modeling-conventions.md §3.1.
 *
 * STORED vs DERIVED (D14, option (a) — the worthiness axis is stored ONLY as `degradedQty`,
 * always quantified). The X.731 Usage region was dropped (D2 revision); Fill is a domain
 * region; Operational/AvailabilityStatus/Fill are DERIVED total functions of the stored fields.
 *
 * NON-NEGATIVE CONE (D12): all stored quantities are ZERO or all-positive — `ConeNonNegative`.
 * That (and the order-dependent derived funs) need the `keyed_order` premise; the TEST ROOT
 * assumes `ringAxioms and orderAxioms` (kept a premise so non-inventory value users don't pay).
 */

// ── module-local value / handle types ──────────────────────────────────────────────
/** LicensePlate — an InventoryItem's handling-unit identity (D9), distinct from `eId`;
    opaque; non-reusable, unique per tenant (we enforce global uniqueness here). Structure
    deferred (proposed topic). */
sig LicensePlate {}
/** SerialNumber — a product-instance individualizer (D10); opaque; unique within (tenant, Item).
    Presence ⇒ the item is "serialized" (all-or-nothing — an operation-level rule). */
sig SerialNumber {}
/** LotNumber — a lot/batch individualizer (D11); opaque; an InventoryItem holds a SET (commingled
    provenance — not a per-unit discriminator, excluded from the cell key). */
sig LotNumber {}
/** Text — an opaque free-text value (a String); carries the AdjustProperties-editable
    descriptive attributes `notes` and `colorCode`. */
sig Text {}
/** Individualizer — generic placeholder for future individualizers (D3); serialNumber and
    lotNumbers are the concrete ones so far. */
sig Individualizer {}

// ── region value sets ───────────────────────────────────────────────────────────────
/** OperationalState — worthiness for consumption (DERIVED, D14): ENABLED (some available) vs
    DISABLED (on-hand present but entirely unavailable). */
enum OperationalState { ENABLED, DISABLED }
/** AvailabilityStatus — X.731 availability-status qualifier (DERIVED): DEGRADED = ENABLED but a
    non-empty portion is unavailable. `FAILED`/`IN_TEST`/… reserved (not in v1). */
enum AvailabilityStatus { DEGRADED }
/** FillState — stock-fill level (DERIVED, D14): FULL (= maxQty) / PARTIAL / EMPTY (= zero). */
enum FillState { FULL, PARTIAL, EMPTY }
/** AdministrativeState — authorization / hold (STORED; set by Lock/Unlock): UNLOCKED / LOCKED.
    `SHUTTING_DOWN` reserved for the reservations era — not modeled in v1. */
enum AdministrativeState { UNLOCKED, LOCKED }

// ── the entity ──────────────────────────────────────────────────────────────────────
/** InventoryItem — a discrete, homogeneous, non-overlapping amount of goods under a tenant,
    classified by an Item (DT-004). Worthiness stored as `degradedQty`; Operational/Fill derived.
    Identity fields immutable; state fields `var` (the effective timeline). */
sig InventoryItem extends Scoped {
  // identity & classification (IMMUTABLE — constant across the trace)
  itemRef:             one EntityId,          // → Item (required, immutable — D1/G7)
  licensePlate:        one LicensePlate,      // handling-unit identity (D9); immutable, globally unique
  serialNumber:        lone SerialNumber,     // D10 individualizer; immutable, persists (even through empty)
  minQuantity:         one Quantity,          // reorder threshold (default zero); not used by Fill
  maxQuantity:         lone Quantity,         // capacity; drives FULL
  individualizers:     set Individualizer,    // D3 placeholder
  // administrative region (STATE)
  var administrativeState: one AdministrativeState,
  // worthiness (STATE): the UNAVAILABLE portion; absent ⇒ fully available (option (a), D14)
  var degradedQty:         lone Quantity,
  // on-hand (STATE): may be zero (EMPTY)
  var actualQuantity:      one Quantity,
  // individualizers (STATE)
  var lotNumbers:          set LotNumber,       // D11 (commingled)
  // location (STATE)
  var locator:             lone PhysicalLocator,
  // descriptive, AdjustProperties-editable (STATE)
  var notes:               lone Text,
  var colorCode:           lone Text
}

/** Live — the InventoryItems that currently EXIST (the existence axis, varying over the trace):
    Create adds an item; Delete / WriteOff / the absorbed side of Merge remove it. Domain
    invariants below bind only Live items — a not-yet-created or retired atom is "outside the
    world" and its state is unconstrained. */
var sig Live in InventoryItem {}

/** Retired — items removed from existence (Delete / WriteOff / Merge-absorbed). MONOTONIC and
    disjoint from Live: a retired atom (with its immutable license plate) never returns — this is
    D9/G5 non-reusability across time, and it makes Delete TERMINAL. (Depletion to EMPTY does NOT
    retire — that is the Delete-vs-deplete distinction: a depleted item stays Live and is revivable
    by Replenish.) */
var sig Retired in InventoryItem {}
fact ExistenceAxis {
  always (no (Live & Retired))        // an item is never simultaneously live and retired
  always (Retired in Retired')        // retirement is forever (monotonic)
}

// ── DERIVED properties (D14) — total functions of the stored fields, no stored backing ──────
/** availableQty — the consumable amount = actual − degradedQty (= actual when no degradedQty). */
fun InventoryItem.availableQty: Unit -> lone Scalar {
  add[this.actualQuantity.byUnit, negate[this.degradedQty.byUnit]]   // degradedQty absent ⇒ zero map ⇒ = actual
}

/** operationalState — DISABLED iff on-hand is non-empty yet nothing is available (degradedQty =
    actual); otherwise ENABLED. (EMPTY ⇒ ENABLED automatically.) */
fun InventoryItem.operationalState: one OperationalState {
  (isZero[this.availableQty] and not isZero[this.actualQuantity.byUnit]) => DISABLED else ENABLED
}

/** availabilityStatus — contains DEGRADED iff some degradedQty AND some availableQty remains
    (0 < degradedQty < actual); else empty. */
fun InventoryItem.availabilityStatus: set AvailabilityStatus {
  (some this.degradedQty and not isZero[this.availableQty]) => DEGRADED else none
}

/** fillState — EMPTY iff actual is zero; FULL iff maxQty present and actual resolvably-equals it;
    else PARTIAL. */
fun InventoryItem.fillState: one FillState {
  isZero[this.actualQuantity.byUnit] => EMPTY
  else (some this.maxQuantity and semanticEq[this.actualQuantity.byUnit, this.maxQuantity.byUnit] = EQUAL) => FULL
  else PARTIAL
}

/** isSerialized — the item carries a serial number (D10). */
pred isSerialized[ii: InventoryItem] { some ii.serialNumber }

// ── structural facts — IMMUTABLE fields, hold across the whole trace (no `always` needed) ────
// Outgoing soft references: the classifier only (lotNumbers/serialNumber/licensePlate are
// module-local value/handle atoms, not EntityId references).
fact InventoryItemRefs { all ii: InventoryItem | ii.dataRefs = ii.itemRef }

// A resolved classifier is actually an Item (dangling/cross-Universe allowed — soft ref).
fact ItemClassifierIntegrity {
  all ii: InventoryItem | let i = resolve[ii.itemRef] | some i implies i in Item
}

// D9 / G5 — license plates are unique (no two items EVER share one). Because `licensePlate` is
// immutable and this ranges over ALL atoms (live or retired), it also gives NON-REUSABILITY for
// free: a retired item's atom keeps its plate forever, so no other atom can take it.
fact LicensePlateUnique { all disj a, b: InventoryItem | a.licensePlate != b.licensePlate }

// D10 / G6 — a present serialNumber is unique within (tenant, Item). Distinct Items (or tenants)
// may reuse a serial value. Immutable ⇒ holds across the trace.
fact SerialNumberUniquePerItem {
  all disj a, b: InventoryItem |
    (a.tenantId = b.tenantId and a.itemRef = b.itemRef and some a.serialNumber)
      implies a.serialNumber != b.serialNumber
}

// Tight by default — no orphan MODULE-LOCAL handle atoms tied to IMMUTABLE fields. (Quantity /
// PhysicalLocator are SHARED value objects, orphan-EXEMPT, D8.)
fact NoOrphanLicensePlate   { all x: LicensePlate   | x in InventoryItem.licensePlate }
fact NoOrphanSerialNumber   { all x: SerialNumber   | x in InventoryItem.serialNumber }
fact NoOrphanIndividualizer { all x: Individualizer | x in InventoryItem.individualizers }
// State-referenced value atoms: referenced by some item at SOME state (temporal generalization).
fact NoOrphanLotNumber      { all x: LotNumber | eventually some lotNumbers.x }
fact NoOrphanText           { all x: Text      | eventually some (notes + colorCode).x }

// ── per-state domain invariants — bind LIVE items at EVERY state (`always`) ───────────────────
// Meaningful under the keyed_order premise (ringAxioms + orderAxioms), which the test root
// assumes. As `always` facts, every Live InventoryItem is in the cone in every state by construction.
// G1 / D12 — every stored quantity is ZERO or all-positive (the non-negative cone); `maxQuantity`,
// when present, is strictly positive (a zero capacity is degenerate — would collide EMPTY/FULL).
fact ConeNonNegative {
  always all ii: Live |
    classify[ii.actualQuantity.byUnit] in (ZERO + POSITIVE)
    and classify[ii.minQuantity.byUnit] in (ZERO + POSITIVE)          // min: ≥ 0 (Zero = no threshold)
    and (some ii.maxQuantity  implies classify[ii.maxQuantity.byUnit] = POSITIVE)   // max (if present): strictly > 0
    and (some ii.degradedQty  implies classify[ii.degradedQty.byUnit] in (ZERO + POSITIVE))
}

// G3 — EMPTY ⟹ no degradedQty and no lotNumbers (so derived operational is ENABLED, no DEGRADED).
fact EmptyHasNoQualifiers {
  always all ii: Live |
    isZero[ii.actualQuantity.byUnit] implies (no ii.degradedQty and no ii.lotNumbers)
}

// G4 — degradedQty (when present): strictly positive and ≤ actual (component-wise), so
// availableQty ≥ 0. degradedQty = actual ⇒ availableQty = 0 ⇒ derived DISABLED (kept, NOT dropped —
// it is what the derivation reads). keys ⊆ actual's keys follows from `lte` + the cone.
fact DegradedBelowActual {
  always all ii: Live | some ii.degradedQty implies (
    not isZero[ii.degradedQty.byUnit]                          // > 0
    and lte[ii.degradedQty.byUnit, ii.actualQuantity.byUnit]   // ≤ actual
  )
}
