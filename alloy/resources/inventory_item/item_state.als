module resources/inventory_item/item_state

/*
 * InventoryItemState — the reified STATE RECORD of an InventoryItem (DT-006 build; the decision is
 * design-topics/dt-006 §Build preparation): the mutable payload of the entity, packaged as a value
 * (a `Snapshot`), so occurrences can carry the state they read (`pre`) and produced (`post`), and
 * state-at-t is LOCF of records — the ONLY reducer. Identity (eId, itemRef, licensePlate,
 * serialNumber, minQuantity) stays on the InventoryItem atom; EXISTENCE stays OUT of the record
 * (it is the occurrence-log projection `liveAt`, see occurrences.als).
 *
 * The intra-snapshot invariants (cone, fill-empty, degraded≤actual, empty-has-no-qualifiers) are
 * FACTS on the record: they define what a WELL-FORMED state IS (value well-formedness, like
 * `nf[byUnit]` on Quantity) and therefore hold at every tick for free. Operation-level legality is
 * NOT here — it is guard-derived in the occurrence layer (the invariant role-change).
 *
 * This record doubles as the future bitemporal VERSION PAYLOAD (meta/bitemporal).
 */

open meta/action/stateful                      // Snapshot
open shared/values                             // Quantity (byUnit), PhysicalLocator
open meta/keyed_value_algebra/keyed_order      // classify/Sign, lte, isZero (+ keyed_monoid: add, negate)
open resources/inventory_item/inventory_item   // FillState, AdministrativeState, LotNumber, Text enums/handles

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

// ── intra-snapshot invariants (well-formedness of a state; meaningful under the keyed_order
//    premises, which every root in this cone assumes — same as the var model) ─────────────────────
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
