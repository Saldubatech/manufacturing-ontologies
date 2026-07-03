module resources/inventory_item/inventory_item_types

/*
 * INVENTORY ITEM — TYPES (DT-017 four-file architecture: types / contracts / implementation /
 * mock). Everything a consumer may SEE: the identity-only entity, the state record
 * (InventoryItemState), the REIFIED OBSERVABLES (`stateRel`, `liveTicks`) with their read API
 * (`stateAt`/`liveAt` — same signatures as the former occurrence-layer projections), and the
 * definitional facts that make the data well-formed. The module's LAWS about observable
 * behavior are named predicates in inventory_item_contracts.als; the log machinery that
 * realizes them (kinds, guards, chaining, LOCF bridge) is inventory_item_implementation.als.
 *
 * Absorbs the former inventory_item.als (entity) + item_state.als (record) — strict renames,
 * 2026-07-03. The entity remains IDENTITY ONLY (DT-011): the observables are relations the
 * implementation DERIVES from the committed log; in consumer unit roots they are constrained
 * only by the contract (opening inventory_item_mock.als IS assuming it).
 */

open meta/profiles/domain_log                  // PROFILE (DT-012): log anatomy + group/order premises for the whole cone
open meta/kernel                               // Entity/Scoped, EntityId, resolve, refs
open meta/action/stateful                      // Snapshot (the record's supertype); Tick via the anatomy
open shared/values                             // Quantity (minQuantity, sActual), PhysicalLocator
open meta/keyed_value_algebra/keyed_order      // classify/Sign, lte, isZero (+ keyed_monoid: add, negate)
open reference_data/item/item_types            // Item — the primary classifier (TYPES only; laws by mock/implementation)

// ── module-local value / handle types ──────────────────────────────────────────────
/** LicensePlate — an InventoryItem's handling-unit identity (D9), distinct from `eId`;
    opaque; non-reusable, unique per tenant (we enforce global uniqueness here). Structure
    deferred (proposed topic). */
sig LicensePlate {}
/** SerialNumber — a product-instance individualizer (D10); opaque; unique within (tenant, Item).
    Presence ⇒ the item is "serialized" (all-or-nothing — an operation-level rule). */
sig SerialNumber {}
/** LotNumber — a lot/batch individualizer (D11); opaque; a state carries a SET (commingled
    provenance — not a per-unit discriminator, excluded from the cell key). */
sig LotNumber {}
/** Text — an opaque free-text value (a String); carries the AdjustProperties-editable
    descriptive attributes (notes, colorCode) on the state record. */
sig Text {}
/** Individualizer — generic placeholder for future individualizers (D3); serialNumber and
    lotNumbers are the concrete ones so far. */
sig Individualizer {}

// ── region value sets (the state record's enums) ─────────────────────────────────────────────
/** OperationalState — worthiness for consumption (DERIVED, D14): ENABLED vs DISABLED. */
enum OperationalState { ENABLED, DISABLED }
/** AvailabilityStatus — X.731 availability-status qualifier (DERIVED): DEGRADED. */
enum AvailabilityStatus { DEGRADED }
/** FillState — stock-fill level (D16): SEALED (operator-asserted as-intended), OPEN (working),
    EMPTY (zero; EMPTY ⟺ actual = 0 — a record fact). */
enum FillState { SEALED, OPEN, EMPTY }
/** AdministrativeState — authorization / hold (set by Lock/Unlock): UNLOCKED / LOCKED. */
enum AdministrativeState { UNLOCKED, LOCKED }

// ── the entity: IDENTITY + the reified observables ───────────────────────────────────────────
/** InventoryItem — the identity of a discrete amount of goods under a tenant, classified by an
    Item; its mutable payload lives on `InventoryItemState` records in the occurrence log,
    surfaced here as the derived observables `stateRel`/`liveTicks`. */
sig InventoryItem extends Scoped {
  itemRef:         one EntityId,          // → Item (required, immutable — D1/G7)
  licensePlate:    one LicensePlate,      // handling-unit identity (D9); immutable, globally unique
  serialNumber:    lone SerialNumber,     // D10 individualizer; immutable, persists (even through empty)
  minQuantity:     one Quantity,          // reorder threshold (default zero); not used by Fill
  individualizers: set Individualizer,    // D3 placeholder
  // — REIFIED OBSERVABLES (DT-017): derived by the implementation's bridge facts; constrained
  //   only by the contract in unit roots. Arity watch: stateRel is the module's one arity-3 field.
  stateRel:        Tick -> lone InventoryItemState,   // payload as of each tick (LOCF; tombstone once retired)
  liveTicks:       set Tick                           // the ticks at which the item EXISTS
}

/** isSerialized — the item carries a serial number (D10). */
pred isSerialized[ii: InventoryItem] { some ii.serialNumber }

// ── the read API (same signatures as the former occurrence-layer projections) ────────────────
/** stateAt — LOCF of records: ii's payload as of `t` (its tombstone once retired — check liveAt). */
fun stateAt[ii: InventoryItem, t: Tick]: lone InventoryItemState { ii.stateRel[t] }
/** liveAt — the existence projection: created, and the last touch did not retire it. */
pred liveAt[ii: InventoryItem, t: Tick] { t in ii.liveTicks }

// ── the state record (the mutable payload as a VALUE; DT-006) ─────────────────────────────────
/** InventoryItemState — one moment's mutable payload of an InventoryItem (a value; extensional). */
sig InventoryItemState extends Snapshot {
  sFill:       one  FillState,
  sAdmin:      one  AdministrativeState,
  sActual:     one  Quantity,
  sDegraded:   lone Quantity,
  sLots:       set  LotNumber,
  sLocator:    lone PhysicalLocator,
  sNotes:      lone Text,
  sColorCode:  lone Text,
  sExpiration: lone Int            // D17 placeholder (Int timestamp) — re-base on Instant with DT-001.03
}

// Value semantics: a state IS its fields — no two record atoms carry identical payloads.
fact StateExtensional {
  all disj a, b: InventoryItemState |
    a.sFill != b.sFill or a.sAdmin != b.sAdmin or a.sActual != b.sActual
    or a.sDegraded != b.sDegraded or a.sLots != b.sLots or a.sLocator != b.sLocator
    or a.sNotes != b.sNotes or a.sColorCode != b.sColorCode or a.sExpiration != b.sExpiration
}

// ── intra-snapshot invariants (DEFINITIONAL: what a well-formed state IS — value
//    well-formedness, like `nf[byUnit]` on Quantity; they hold at every tick for free.
//    Operation-level legality is guard-derived in the implementation.) ──────────────────────────
// G1/D12 — the non-negative cone.
fact SConeNonNegative {
  all s: InventoryItemState |
    classify[s.sActual.byUnit] in (ZERO + POSITIVE)
    and (some s.sDegraded implies classify[s.sDegraded.byUnit] in (ZERO + POSITIVE))
}
// D6/D16 — EMPTY ⟺ actual = 0.
fact SFillEmptyConsistency {
  all s: InventoryItemState | s.sFill = EMPTY iff isZero[s.sActual.byUnit]
}
// G3 — EMPTY ⟹ no qualifiers.
fact SEmptyHasNoQualifiers {
  all s: InventoryItemState | isZero[s.sActual.byUnit] implies (no s.sDegraded and no s.sLots)
}
// G4 — degraded (when present): strictly positive and ≤ actual.
fact SDegradedBelowActual {
  all s: InventoryItemState | some s.sDegraded implies
    (not isZero[s.sDegraded.byUnit] and lte[s.sDegraded.byUnit, s.sActual.byUnit])
}

// ── derived properties (the record-level twins of the entity's derived funs) ─────────────────────
/** sAvailableQty — the consumable amount = actual − degraded. */
fun InventoryItemState.sAvailableQty: Unit -> lone Scalar {
  add[this.sActual.byUnit, negate[this.sDegraded.byUnit]]
}
/** sOperationalState — DISABLED iff non-empty yet nothing available; else ENABLED. */
fun InventoryItemState.sOperationalState: one OperationalState {
  (isZero[this.sAvailableQty] and not isZero[this.sActual.byUnit]) => DISABLED else ENABLED
}

// ── definitional structural facts (all identity fields immutable — plain, non-temporal) ─────────
// Outgoing soft references: the classifier only.
fact InventoryItemRefs { all ii: InventoryItem | ii.dataRefs = ii.itemRef }

// A resolved classifier is actually an Item (dangling/cross-Universe allowed — soft ref).
fact ItemClassifierIntegrity {
  all ii: InventoryItem | let i = resolve[ii.itemRef] | some i implies i in Item
}

// D9 / G5 — license plates are unique (no two items EVER share one); non-reusability comes from the
// log's no-resurrection guard (implementation) rather than a Retired axis.
fact LicensePlateUnique { all disj a, b: InventoryItem | a.licensePlate != b.licensePlate }

// D10 / G6 — a present serialNumber is unique within (tenant, Item).
fact SerialNumberUniquePerItem {
  all disj a, b: InventoryItem |
    (a.tenantId = b.tenantId and a.itemRef = b.itemRef and some a.serialNumber)
      implies a.serialNumber != b.serialNumber
}

// Tight by default — no orphan handle atoms tied to the IMMUTABLE identity. (LotNumber/Text are
// carried by state records/occurrence params, so their no-orphan rules live at the DAG sink,
// inventory_item_implementation.als; Quantity/PhysicalLocator are shared value objects,
// orphan-EXEMPT, D8.)
fact NoOrphanLicensePlate   { all x: LicensePlate   | x in InventoryItem.licensePlate }
fact NoOrphanSerialNumber   { all x: SerialNumber   | x in InventoryItem.serialNumber }
fact NoOrphanIndividualizer { all x: Individualizer | x in InventoryItem.individualizers }
