module resources/inventory_item/tests/operations

open resources/inventory_item/operations

/*
 * Operation/transition tests for InventoryItem (v1, Phase B). Each `unit_op_*` run exhibits a
 * single firing of an operation (state0 → state1, asserted with `after`); each `unit_rej_*` run
 * pairs an operation with an illegal precondition and expects UNSAT — proving the guard forbids it.
 * Trace-level lifecycle properties (Delete terminal, deplete-vs-delete) live in tests/lifecycle.als.
 */

fact ScalarPremises { ringAxioms and orderAxioms }

// ── operation firings (expect SAT) ────────────────────────────────────────────────────
run unit_op_create_fires { some ii: InventoryItem, q: Quantity | create[ii, q] } for 6 but 3 Scalar
run unit_op_delete_fires { some ii: InventoryItem | delete[ii] } for 6 but 3 Scalar
run unit_op_writeOff_fires { some ii: InventoryItem | writeOff[ii] and ii.fillState != EMPTY } for 6 but 3 Scalar

// Replenish revives a depleted (EMPTY) item — the deplete-is-not-terminal decision.
run unit_op_replenish_revivesEmpty {
  some ii: InventoryItem, q: Quantity |
    ii in Live and ii.fillState = EMPTY and replenish[ii, q, none]
    and after (ii in Live and ii.fillState != EMPTY)
} for 6 but 3 Scalar

// Consume-to-zero leaves a Live husk that is EMPTY ⟹ ENABLED (qualifiers cleared).
run unit_op_consume_toZero {
  some ii: InventoryItem, q: Quantity |
    consume[ii, q] and after (ii in Live and ii.fillState = EMPTY and ii.operationalState = ENABLED and no ii.degradedQty)
} for 6 but 3 Scalar

// Consume the available part of a DEGRADED item exhausts availability → DISABLED husk-of-degraded.
run unit_op_consume_toDisabled {
  some ii: InventoryItem, q: Quantity |
    DEGRADED in ii.availabilityStatus and consume[ii, q]
    and after (not isZero[ii.actualQuantity.byUnit] and ii.operationalState = DISABLED)
} for 6 but 3 Scalar

run unit_op_move_fires { some ii: InventoryItem, loc: PhysicalLocator | move[ii, loc] } for 6 but 3 Scalar

// ForceMove overrides a LOCKED hold (privileged).
run unit_op_forceMove_locked {
  some ii: InventoryItem, loc: PhysicalLocator | ii.administrativeState = LOCKED and forceMove[ii, loc]
} for 6 but 3 Scalar

run unit_op_split_fires { some o, n: InventoryItem, q: Quantity | split[o, n, q, none] } for 6 but 3 Scalar

// Split off ALL the degraded portion: original left ENABLED, the new item DISABLED (isolate spoilage).
run unit_op_split_isolateDegraded {
  some o, n: InventoryItem, d: Quantity |
    DEGRADED in o.availabilityStatus and split[o, n, none, d]
    and after (o.operationalState = ENABLED and n.operationalState = DISABLED)
} for 6 but 3 Scalar

run unit_op_merge_fires { some s, a: InventoryItem | merge[s, a] } for 6 but 3 Scalar
run unit_op_rePack_fires { some ii: InventoryItem, g: Quantity | rePack[ii, g, none] } for 6 but 3 Scalar
run unit_op_adjustQuantity_fires { some ii: InventoryItem, g: Quantity | adjustQuantity[ii, g, none] } for 6 but 3 Scalar

// AdjustQuantity to an observed zero reconciles to EMPTY (clears qualifiers).
run unit_op_adjustQuantity_toZero {
  some ii: InventoryItem, g: Quantity |
    isZero[g.byUnit] and adjustQuantity[ii, g, none] and after (ii.fillState = EMPTY)
} for 6 but 3 Scalar

run unit_op_adjustProperties_fires { some ii: InventoryItem, t: Text | adjustProperties[ii, t, none] } for 6 but 3 Scalar

// Inspect sets degradedQty = actual → DISABLED; Inspect with none clears → ENABLED.
run unit_op_inspect_toDisabled {
  some ii: InventoryItem, d: Quantity |
    inspect[ii, d] and after ii.operationalState = DISABLED
} for 6 but 3 Scalar
run unit_op_inspect_clears {
  some ii: InventoryItem |
    some ii.degradedQty and inspect[ii, none] and after (no ii.degradedQty and ii.operationalState = ENABLED)
} for 6 but 3 Scalar

run unit_op_lock_fires { some ii: InventoryItem | lock[ii] } for 6 but 3 Scalar
run unit_op_unlock_fires { some ii: InventoryItem | unlock[ii] } for 6 but 3 Scalar

// ── guard rejections (expect UNSAT — the guard forbids the illegal precondition) ──────────
run unit_rej_delete_nonEmpty { some ii: InventoryItem | delete[ii] and ii.fillState != EMPTY } for 6 but 3 Scalar
run unit_rej_consume_locked { some ii: InventoryItem, q: Quantity | consume[ii, q] and ii.administrativeState = LOCKED } for 6 but 3 Scalar
run unit_rej_consume_disabled { some ii: InventoryItem, q: Quantity | consume[ii, q] and ii.operationalState = DISABLED } for 6 but 3 Scalar
run unit_rej_consume_overdraw {
  some ii: InventoryItem, q: Quantity | consume[ii, q] and not lte[q.byUnit, ii.availableQty]
} for 6 but 3 Scalar
run unit_rej_move_locked { some ii: InventoryItem, loc: PhysicalLocator | move[ii, loc] and ii.administrativeState = LOCKED } for 6 but 3 Scalar
run unit_rej_split_serialized { some o, n: InventoryItem, q: Quantity | split[o, n, q, none] and isSerialized[o] } for 6 but 3 Scalar
run unit_rej_merge_serialized { some s, a: InventoryItem | merge[s, a] and isSerialized[s] } for 6 but 3 Scalar
run unit_rej_merge_differentItem { some s, a: InventoryItem | merge[s, a] and s.itemRef != a.itemRef } for 6 but 3 Scalar
run unit_rej_rePack_empty { some ii: InventoryItem, g: Quantity | rePack[ii, g, none] and ii.fillState = EMPTY } for 6 but 3 Scalar
run unit_rej_rePack_serialized { some ii: InventoryItem, g: Quantity | rePack[ii, g, none] and isSerialized[ii] } for 6 but 3 Scalar
run unit_rej_replenish_locked { some ii: InventoryItem, q: Quantity | replenish[ii, q, none] and ii.administrativeState = LOCKED } for 6 but 3 Scalar
run unit_rej_lock_alreadyLocked { some ii: InventoryItem | lock[ii] and ii.administrativeState = LOCKED } for 6 but 3 Scalar
run unit_rej_create_reuseRetired { some ii: InventoryItem, q: Quantity | create[ii, q] and ii in Retired } for 6 but 3 Scalar
