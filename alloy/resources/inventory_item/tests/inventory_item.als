module resources/inventory_item/tests/inventory_item

open resources/inventory_item/inventory_item

/*
 * Static-shape tests for InventoryItem (v1), now over the TEMPORAL model (Phase B). Each run
 * looks at a single (initial) state; the invariant `check`s are wrapped in `always`, so they are
 * verified at EVERY state of every trace. Quantification is over `Live` (the existence axis):
 * a not-yet-created / retired atom is outside the world and intentionally unconstrained.
 *
 * Illustrate decisions D1–D14: the stored/derived split, the non-negative cone, the worthiness
 * derivation (ENABLED/DEGRADED/DISABLED from degradedQty), Fill, EMPTY⟹ENABLED, LPN/serial
 * uniqueness, commingled lots, and the forbidden (negative / EMPTY×degraded / degraded>actual /
 * serial-dup / zero-max) states. Operation/transition tests live in tests/operations.als.
 */

// The keyed_order premise — a commutative-ring Scalar with a posited total order. Under it the
// cone and the `classify`/`semanticEq`-based derived funs are meaningful (kept out of the library
// so non-inventory value-users don't pay to solve a ring).
fact ScalarPremises { ringAxioms and orderAxioms }

// ── coherence / reachable states (expect SAT) ─────────────────────────────────────────

// Healthy: UNLOCKED, ENABLED, some stock, classifier resolves to an Item.
run unit_inventoryItem_healthy {
  some ii: Live, i: Item |
    resolve[ii.itemRef] = i
    and ii.administrativeState = UNLOCKED
    and ii.operationalState = ENABLED
    and no ii.degradedQty
    and not isZero[ii.actualQuantity.byUnit]
} for 5 but 3 Scalar

// DEGRADED: a non-empty unavailable portion, but some available remains.
run unit_inventoryItem_degraded {
  some ii: Live |
    DEGRADED in ii.availabilityStatus and ii.operationalState = ENABLED and not isZero[ii.availableQty]
} for 5 but 3 Scalar

// DISABLED: stock present but nothing available (degradedQty = actual).
run unit_inventoryItem_disabled {
  some ii: Live |
    ii.operationalState = DISABLED and not isZero[ii.actualQuantity.byUnit] and isZero[ii.availableQty]
} for 5 but 3 Scalar

// LOCKED with stock (administrative hold is orthogonal to fill/worthiness).
run unit_inventoryItem_locked {
  some ii: Live | ii.administrativeState = LOCKED and not isZero[ii.actualQuantity.byUnit]
} for 5 but 3 Scalar

// FULL: actual resolvably-equals maxQty.
run unit_inventoryItem_full { some ii: Live | ii.fillState = FULL } for 5 but 3 Scalar

// Commingled lots: an item holding ≥ 2 lot numbers (D11).
run unit_inventoryItem_commingledLots { some ii: Live | gt[#ii.lotNumbers, 1] } for 5 but 3 Scalar

// Serialized item (D10).
run unit_inventoryItem_serialized { some ii: Live | isSerialized[ii] } for 5 but 3 Scalar

// Same serial reused across DIFFERENT Items is allowed (serial unique only per (tenant, Item)).
run unit_inventoryItem_serialReuseAcrossItems {
  some disj a, b: Live |
    some a.serialNumber and a.serialNumber = b.serialNumber and a.itemRef != b.itemRef
} for 6 but 3 Scalar

// Descriptive properties (AdjustProperties-editable): an item with notes and colorCode.
run unit_inventoryItem_descriptive {
  some ii: Live | some ii.notes and some ii.colorCode
} for 5 but 3 Scalar

// ── invariants (check; UNSAT = holds) — `always`, so verified in every state ──────────────

// EMPTY ⟹ ENABLED: the four EMPTY×{DEGRADED,DISABLED} states are impossible.
assert unit_inventoryItem_emptyImpliesEnabled {
  always no ii: Live |
    ii.fillState = EMPTY and (ii.operationalState = DISABLED or DEGRADED in ii.availabilityStatus)
}
check unit_inventoryItem_emptyImpliesEnabled for 6 but 3 Scalar

// availableQty is never negative (cone consequence).
assert unit_inventoryItem_availableNonNegative {
  always all ii: Live | classify[ii.availableQty] in (ZERO + POSITIVE)
}
check unit_inventoryItem_availableNonNegative for 6 but 3 Scalar

// Worthiness derivation: DEGRADED ⟹ ENABLED ∧ available>0; DISABLED ⟺ stock present ∧ available=0.
assert unit_inventoryItem_worthinessDerivation {
  always all ii: Live |
    (DEGRADED in ii.availabilityStatus implies (ii.operationalState = ENABLED and not isZero[ii.availableQty]))
    and (ii.operationalState = DISABLED iff (not isZero[ii.actualQuantity.byUnit] and isZero[ii.availableQty]))
}
check unit_inventoryItem_worthinessDerivation for 6 but 3 Scalar

// FULL ⟺ non-empty ∧ maxQty present ∧ actual resolvably-equals it. (The non-empty guard
// matters: an EMPTY item whose maxQty is also the zero-Quantity is EMPTY, not FULL.)
assert unit_inventoryItem_fullDefinition {
  always all ii: Live |
    ii.fillState = FULL iff
      (not isZero[ii.actualQuantity.byUnit]
       and some ii.maxQuantity
       and semanticEq[ii.actualQuantity.byUnit, ii.maxQuantity.byUnit] = EQUAL)
}
check unit_inventoryItem_fullDefinition for 6 but 3 Scalar

// License plates are unique across items (D9) — immutable, so this is a whole-trace property.
assert unit_inventoryItem_lpnUnique { all disj a, b: InventoryItem | a.licensePlate != b.licensePlate }
check unit_inventoryItem_lpnUnique for 6 but 3 Scalar

// Cross-tenant isolation on the classifier reference (kernel regression).
assert unit_inventoryItem_tenantIsolation {
  all ii: InventoryItem | let i = resolve[ii.itemRef] | i in Scoped implies ii.tenantId = i.tenantId
}
check unit_inventoryItem_tenantIsolation for 6 but 3 Scalar

// ── negative scenarios (expect UNSAT — the design forbids them, in every state) ───────────

// No negative stored quantity (the cone).
run unit_inventoryItem_negActualImpossible {
  some ii: Live | classify[ii.actualQuantity.byUnit] = NEGATIVE
} for 5 but 3 Scalar

// No degradedQty on an EMPTY item.
run unit_inventoryItem_emptyDegradedImpossible {
  some ii: Live | isZero[ii.actualQuantity.byUnit] and some ii.degradedQty
} for 5 but 3 Scalar

// No degradedQty exceeding actual.
run unit_inventoryItem_degradedAboveActualImpossible {
  some ii: Live | some ii.degradedQty and not lte[ii.degradedQty.byUnit, ii.actualQuantity.byUnit]
} for 5 but 3 Scalar

// No duplicate serial within the same (tenant, Item).
run unit_inventoryItem_serialDupImpossible {
  some disj a, b: Live |
    a.tenantId = b.tenantId and a.itemRef = b.itemRef and some a.serialNumber and a.serialNumber = b.serialNumber
} for 6 but 3 Scalar

// No zero-capacity item: maxQuantity, when present, is strictly positive (a zero capacity is degenerate).
run unit_inventoryItem_zeroMaxImpossible {
  some ii: Live | some ii.maxQuantity and isZero[ii.maxQuantity.byUnit]
} for 5 but 3 Scalar
