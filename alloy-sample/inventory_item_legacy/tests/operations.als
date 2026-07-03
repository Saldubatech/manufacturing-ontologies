module resources/inventory_item/legacy/tests/operations

open resources/inventory_item/legacy/operations

/*
 * Operation/transition tests for InventoryItem (v1, Phase B). Each `unit_op_*` run exhibits a
 * single firing of an operation (state0 → state1, asserted with `after`); each `unit_rej_*` run
 * pairs an operation with an illegal precondition and expects UNSAT — proving the guard forbids it.
 * Trace-level lifecycle properties (Delete terminal, deplete-vs-delete) live in tests/lifecycle.als.
 */

fact ScalarPremises { ringAxioms and orderAxioms }

// ── operation firings (expect SAT) ────────────────────────────────────────────────────
run unit_op_create_fires { some ii: InventoryItem, q: Quantity | create[ii, q, none] } for 6 but 3 Scalar expect 1

// D16 Fill state machine — created OPEN; `seal`→SEALED; `unseal`→OPEN; a quantity change demotes
// SEALED→OPEN; rePack/Move preserve SEALED; split-off born OPEN.
run unit_op_create_isOpen {
  some ii: InventoryItem, q: Quantity | create[ii, q, none] and after ii.fillState = OPEN
} for 6 but 3 Scalar expect 1
run unit_op_seal_sealsOpen {
  some ii: InventoryItem | ii.fillState = OPEN and seal[ii] and after ii.fillState = SEALED
} for 6 but 3 Scalar expect 1
run unit_op_unseal_opensSealed {
  some ii: InventoryItem | ii.fillState = SEALED and unseal[ii] and after ii.fillState = OPEN
} for 6 but 3 Scalar expect 1
run unit_op_consume_demotesSealed {
  some ii: InventoryItem, q: Quantity |
    ii.fillState = SEALED and consume[ii, q] and after (ii.fillState = OPEN)   // a real draw breaks the seal
} for 6 but 3 Scalar expect 1
run unit_op_rePack_preservesSealed {
  some ii: InventoryItem, g: Quantity |
    ii.fillState = SEALED and rePack[ii, g, none] and after ii.fillState = SEALED   // re-expression keeps SEALED
} for 6 but 3 Scalar expect 1
run unit_op_move_preservesSealed {
  some ii: InventoryItem, loc: PhysicalLocator |
    ii.fillState = SEALED and move[ii, loc] and after ii.fillState = SEALED
} for 6 but 3 Scalar expect 1
run unit_op_split_bornOpen {
  some o, n: InventoryItem, q: Quantity | split[o, n, q, none] and after n.fillState = OPEN
} for 6 but 3 Scalar expect 1
run unit_op_delete_fires { some ii: InventoryItem | delete[ii] } for 6 but 3 Scalar expect 1
run unit_op_writeOff_fires { some ii: InventoryItem | writeOff[ii] and ii.fillState != EMPTY } for 6 but 3 Scalar expect 1

// Replenish revives a depleted (EMPTY) item — the deplete-is-not-terminal decision.
run unit_op_replenish_revivesEmpty {
  some ii: InventoryItem, q: Quantity |
    ii in Live and ii.fillState = EMPTY and replenish[ii, q, none, none]
    and after (ii in Live and ii.fillState != EMPTY)
} for 6 but 3 Scalar expect 1

// Consume-to-zero leaves a Live husk that is EMPTY ⟹ ENABLED (qualifiers cleared).
run unit_op_consume_toZero {
  some ii: InventoryItem, q: Quantity |
    consume[ii, q] and after (ii in Live and ii.fillState = EMPTY and ii.operationalState = ENABLED and no ii.degradedQty)
} for 6 but 3 Scalar expect 1

// Consume the available part of a DEGRADED item exhausts availability → DISABLED husk-of-degraded.
run unit_op_consume_toDisabled {
  some ii: InventoryItem, q: Quantity |
    DEGRADED in ii.availabilityStatus and consume[ii, q]
    and after (not isZero[ii.actualQuantity.byUnit] and ii.operationalState = DISABLED)
} for 6 but 3 Scalar expect 1

run unit_op_move_fires { some ii: InventoryItem, loc: PhysicalLocator | move[ii, loc] } for 6 but 3 Scalar expect 1

// ForceMove overrides a LOCKED hold (privileged).
run unit_op_forceMove_locked {
  some ii: InventoryItem, loc: PhysicalLocator | ii.administrativeState = LOCKED and forceMove[ii, loc]
} for 6 but 3 Scalar expect 1

run unit_op_split_fires { some o, n: InventoryItem, q: Quantity | split[o, n, q, none] } for 6 but 3 Scalar expect 1

// Split off ALL the degraded portion: original left ENABLED, the new item DISABLED (isolate spoilage).
run unit_op_split_isolateDegraded {
  some o, n: InventoryItem, d: Quantity |
    DEGRADED in o.availabilityStatus and split[o, n, none, d]
    and after (o.operationalState = ENABLED and n.operationalState = DISABLED)
} for 6 but 3 Scalar expect 1

run unit_op_merge_fires { some s, a: InventoryItem | merge[s, a] } for 6 but 3 Scalar expect 1

// D17 expiration — Create sets it; Replenish/Merge take the EARLIER (min); absent = "never".
run unit_op_create_withExpiration {
  some ii: InventoryItem, q: Quantity | create[ii, q, 4] and after ii.expirationDate = 4
} for 6 but 3 Scalar expect 1
run unit_op_merge_minExpiration {
  some s, a: InventoryItem | s.expirationDate = 3 and a.expirationDate = 7 and merge[s, a] and after s.expirationDate = 3
} for 6 but 3 Scalar expect 1
run unit_op_replenish_shortensExpiration {
  some ii: InventoryItem, q: Quantity | ii.expirationDate = 7 and replenish[ii, q, none, 3] and after ii.expirationDate = 3
} for 6 but 3 Scalar expect 1
run unit_op_replenish_neverKeepsExpiration {
  some ii: InventoryItem, q: Quantity | ii.expirationDate = 5 and replenish[ii, q, none, none] and after ii.expirationDate = 5
} for 6 but 3 Scalar expect 1
run unit_op_rePack_fires { some ii: InventoryItem, g: Quantity | rePack[ii, g, none] } for 6 but 3 Scalar expect 1
run unit_op_adjustQuantity_fires { some ii: InventoryItem, g: Quantity | adjustQuantity[ii, g, none] } for 6 but 3 Scalar expect 1

// AdjustQuantity to an observed zero reconciles to EMPTY (clears qualifiers).
run unit_op_adjustQuantity_toZero {
  some ii: InventoryItem, g: Quantity |
    isZero[g.byUnit] and adjustQuantity[ii, g, none] and after (ii.fillState = EMPTY)
} for 6 but 3 Scalar expect 1

run unit_op_adjustProperties_fires { some ii: InventoryItem, t: Text | adjustProperties[ii, t, none] } for 6 but 3 Scalar expect 1

// Inspect sets degradedQty = actual → DISABLED; Inspect with none clears → ENABLED.
run unit_op_inspect_toDisabled {
  some ii: InventoryItem, d: Quantity |
    inspect[ii, d] and after ii.operationalState = DISABLED
} for 6 but 3 Scalar expect 1
run unit_op_inspect_clears {
  some ii: InventoryItem |
    some ii.degradedQty and inspect[ii, none] and after (no ii.degradedQty and ii.operationalState = ENABLED)
} for 6 but 3 Scalar expect 1

run unit_op_lock_fires { some ii: InventoryItem | lock[ii] } for 6 but 3 Scalar expect 1
run unit_op_unlock_fires { some ii: InventoryItem | unlock[ii] } for 6 but 3 Scalar expect 1

// ── guard rejections (expect UNSAT — the guard forbids the illegal precondition) ──────────
run unit_rej_delete_nonEmpty { some ii: InventoryItem | delete[ii] and ii.fillState != EMPTY } for 6 but 3 Scalar expect 0
run unit_rej_consume_locked { some ii: InventoryItem, q: Quantity | consume[ii, q] and ii.administrativeState = LOCKED } for 6 but 3 Scalar expect 0
run unit_rej_consume_disabled { some ii: InventoryItem, q: Quantity | consume[ii, q] and ii.operationalState = DISABLED } for 6 but 3 Scalar expect 0
run unit_rej_consume_overdraw {
  some ii: InventoryItem, q: Quantity | consume[ii, q] and not lte[q.byUnit, ii.availableQty]
} for 6 but 3 Scalar expect 0
run unit_rej_move_locked { some ii: InventoryItem, loc: PhysicalLocator | move[ii, loc] and ii.administrativeState = LOCKED } for 6 but 3 Scalar expect 0
run unit_rej_split_serialized { some o, n: InventoryItem, q: Quantity | split[o, n, q, none] and isSerialized[o] } for 6 but 3 Scalar expect 0
run unit_rej_merge_serialized { some s, a: InventoryItem | merge[s, a] and isSerialized[s] } for 6 but 3 Scalar expect 0
run unit_rej_merge_differentItem { some s, a: InventoryItem | merge[s, a] and s.itemRef != a.itemRef } for 6 but 3 Scalar expect 0
run unit_rej_rePack_empty { some ii: InventoryItem, g: Quantity | rePack[ii, g, none] and ii.fillState = EMPTY } for 6 but 3 Scalar expect 0
run unit_rej_rePack_serialized { some ii: InventoryItem, g: Quantity | rePack[ii, g, none] and isSerialized[ii] } for 6 but 3 Scalar expect 0
run unit_rej_replenish_locked { some ii: InventoryItem, q: Quantity | replenish[ii, q, none, none] and ii.administrativeState = LOCKED } for 6 but 3 Scalar expect 0
run unit_rej_lock_alreadyLocked { some ii: InventoryItem | lock[ii] and ii.administrativeState = LOCKED } for 6 but 3 Scalar expect 0
run unit_rej_create_reuseRetired { some ii: InventoryItem, q: Quantity | create[ii, q, none] and ii in Retired } for 6 but 3 Scalar expect 0
run unit_rej_seal_empty { some ii: InventoryItem | seal[ii] and ii.fillState = EMPTY } for 6 but 3 Scalar expect 0
run unit_rej_unseal_notSealed { some ii: InventoryItem | unseal[ii] and ii.fillState != SEALED } for 6 but 3 Scalar expect 0
