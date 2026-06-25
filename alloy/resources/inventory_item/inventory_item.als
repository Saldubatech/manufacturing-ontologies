module resources/inventory_item/inventory_item

open meta/kernel                  // Entity/Scoped, EntityId, resolve, refs
open meta/values                  // Quantity (byUnit), PhysicalLocator, Unit
open meta/algebra/keyed_order     // classify/Sign, semanticEq/EqVerdict, lte; (→ keyed_monoid: isZero, add, negate, zero, Scalar, SZero)
open reference_data/item/item     // Item — the primary classifier

/*
 * InventoryItem (v1) — a discrete, homogeneous, non-overlapping amount of goods/materials
 * under a tenant's control, classified by an Item. The STATIC (snapshot) model: structure +
 * invariants + the DERIVED state. Operations (transitions) are the behavioral layer (Phase B,
 * predicate-style) and are NOT modeled here. See workbook resources/inventory_item/.
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
    classified by an Item (DT-004). Worthiness stored as `degradedQty`; Operational/Fill derived. */
sig InventoryItem extends Scoped {
  // identity & classification (stored)
  itemRef:             one EntityId,          // → Item (required, immutable — D1)
  licensePlate:        one LicensePlate,      // handling-unit identity (D9)
  // administrative region (stored)
  administrativeState: one AdministrativeState,
  // worthiness (stored): the UNAVAILABLE portion; absent ⇒ fully available (option (a), D14)
  degradedQty:         lone Quantity,
  // quantity bundle (stored): non-negative cone (D12)
  actualQuantity:      one Quantity,          // on-hand; may be zero (EMPTY)
  minQuantity:         one Quantity,          // reorder threshold (default zero); not used by Fill
  maxQuantity:         lone Quantity,         // capacity; drives FULL
  // individualizers (stored)
  serialNumber:        lone SerialNumber,     // D10
  lotNumbers:          set LotNumber,          // D11 (commingled)
  individualizers:     set Individualizer,     // D3 placeholder
  // location (stored)
  locator:             lone PhysicalLocator,
  // descriptive, AdjustProperties-editable (stored)
  notes:               lone Text,
  colorCode:           lone Text
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

// ── structural facts (order-free) ────────────────────────────────────────────────────
// Outgoing soft references: the classifier only (lotNumbers/serialNumber/licensePlate are
// module-local value/handle atoms, not EntityId references).
fact InventoryItemRefs { all ii: InventoryItem | ii.dataRefs = ii.itemRef }

// A resolved classifier is actually an Item (dangling/cross-Universe allowed — soft ref).
fact ItemClassifierIntegrity {
  all ii: InventoryItem | let i = resolve[ii.itemRef] | some i implies i in Item
}

// G3 — EMPTY ⟹ no degradedQty and no lotNumbers (so derived operational is ENABLED, no DEGRADED).
fact EmptyHasNoQualifiers {
  all ii: InventoryItem |
    isZero[ii.actualQuantity.byUnit] implies (no ii.degradedQty and no ii.lotNumbers)
}

// D9 — license plates are unique (no two items share one). "prefer global".
fact LicensePlateUnique { all disj a, b: InventoryItem | a.licensePlate != b.licensePlate }

// D10 — a present serialNumber is unique within (tenant, Item). Distinct Items (or tenants) may
// reuse a serial value.
fact SerialNumberUniquePerItem {
  all disj a, b: InventoryItem |
    (a.tenantId = b.tenantId and a.itemRef = b.itemRef and some a.serialNumber)
      implies a.serialNumber != b.serialNumber
}

// Tight by default — no orphan MODULE-LOCAL value/handle types. (Quantity / PhysicalLocator are
// SHARED value objects, hence orphan-EXEMPT, D8 — no no-orphan rule here.)
fact NoOrphanLicensePlate   { all x: LicensePlate   | x in InventoryItem.licensePlate }
fact NoOrphanSerialNumber   { all x: SerialNumber   | x in InventoryItem.serialNumber }
fact NoOrphanLotNumber      { all x: LotNumber      | x in InventoryItem.lotNumbers }
fact NoOrphanIndividualizer { all x: Individualizer | x in InventoryItem.individualizers }
fact NoOrphanText           { all x: Text           | x in InventoryItem.(notes + colorCode) }

// ── order-dependent facts (the non-negative cone & degraded bounds) ───────────────────
// Meaningful under the keyed_order premise (ringAxioms + orderAxioms), which the test root
// assumes. Kept as facts (not premise-guarded asserts) so every modeled InventoryItem is in
// the cone by construction.
// G1 / D12 — every stored quantity is ZERO or all-positive (the non-negative cone).
fact ConeNonNegative {
  all ii: InventoryItem |
    classify[ii.actualQuantity.byUnit] in (ZERO + POSITIVE)
    and classify[ii.minQuantity.byUnit] in (ZERO + POSITIVE)
    and (some ii.maxQuantity  implies classify[ii.maxQuantity.byUnit]  in (ZERO + POSITIVE))
    and (some ii.degradedQty  implies classify[ii.degradedQty.byUnit]  in (ZERO + POSITIVE))
}

// G4 — degradedQty (when present): strictly positive and ≤ actual (component-wise), so
// availableQty ≥ 0. degradedQty = actual ⇒ availableQty = 0 ⇒ derived DISABLED (kept, NOT dropped —
// it is what the derivation reads). keys ⊆ actual's keys follows from `lte` + the cone.
fact DegradedBelowActual {
  all ii: InventoryItem | some ii.degradedQty implies (
    not isZero[ii.degradedQty.byUnit]                          // > 0
    and lte[ii.degradedQty.byUnit, ii.actualQuantity.byUnit]   // ≤ actual
  )
}
