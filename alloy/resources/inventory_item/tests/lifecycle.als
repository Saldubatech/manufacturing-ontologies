module resources/inventory_item/tests/lifecycle

open resources/inventory_item/operations

/*
 * Lifecycle / multi-step trace properties for InventoryItem (v1, Phase B). The headline decision
 * under test is deplete-vs-delete: depletion to EMPTY is NOT terminal (the item stays Live and is
 * revivable by Replenish), whereas Delete/WriteOff ARE terminal (the atom + its license plate
 * retire forever). Multi-step runs thread operations with nested `after`; no global trace fact is
 * needed (each run constrains exactly the transitions it exercises).
 */

fact ScalarPremises { ringAxioms and orderAxioms }

// ── deplete-vs-delete (the core lifecycle decision) ───────────────────────────────────────

// Depletion is NOT terminal: consume an item to EMPTY, then Replenish revives it (back to Live, non-empty).
run unit_lc_depletionRevivable {
  some ii: InventoryItem, amt, delta: Quantity |
    ii in Live and ii.fillState != EMPTY
    and consume[ii, amt]
    and after (ii in Live and ii.fillState = EMPTY            // depleted, still Live (not retired)
               and ii not in Retired
               and replenish[ii, delta, none])
    and after after (ii in Live and ii.fillState != EMPTY)    // revived
} for 6 but 3 Scalar

// Consume-to-zero NEVER retires the item — it stays Live (distinguishes deplete from Delete).
assert unit_lc_depletionDoesNotRetire {
  always all ii: InventoryItem, q: Quantity |
    (ii in Live and consume[ii, q]) implies after (ii in Live and ii not in Retired)
}
check unit_lc_depletionDoesNotRetire for 6 but 3 Scalar

// Delete IS terminal: once retired, an item is never Live again (D9/G5 non-reusability across time).
assert unit_lc_deleteTerminal {
  always all ii: InventoryItem | ii in Retired implies always ii not in Live
}
check unit_lc_deleteTerminal for 6 but 3 Scalar

// A deleted item's license plate is never taken by any other item (immutable + global uniqueness).
assert unit_lc_lpnNeverReused {
  always all disj a, b: InventoryItem | a.licensePlate != b.licensePlate
}
check unit_lc_lpnNeverReused for 6 but 3 Scalar

// ── D15 Fill: FULL is one-shot (created/born FULL, never re-entered) ──────────────────────

// Once a live item is not FULL, no operation makes it FULL again (FULL is minted only on a fresh
// atom — by Create, or Split's new split-off). Conditioned on `someOp` so it ranges over real
// operation steps (without it, Alloy's free var-changes could flip fillState spuriously).
assert unit_lc_neverReturnsToFull {
  always (someOp implies all ii: InventoryItem |
    (ii in Live and ii.fillState != FULL) implies after (ii not in Live or ii.fillState != FULL))
}
check unit_lc_neverReturnsToFull for 6 but 3 Scalar

// FULL → (consume) PARTIAL → (consume-to-zero) EMPTY → (replenish) PARTIAL — and never FULL again.
run unit_lc_fullToPartialPermanent {
  some ii: InventoryItem, a1, a2, r: Quantity |
    ii.fillState = FULL
    and consume[ii, a1]
    and after (ii.fillState = PARTIAL and consume[ii, a2])
    and after after (ii.fillState = EMPTY and replenish[ii, r, none])
    and after after after (ii.fillState = PARTIAL)            // revived to PARTIAL, NOT FULL
} for 6 but 3 Scalar

// ── representative end-to-end lifecycle (expect SAT) ──────────────────────────────────────

// Create → Lock → Unlock → Consume-to-zero → Delete: a full birth-to-retirement path.
run unit_lc_fullLifecycle {
  some ii: InventoryItem, q, amt: Quantity |
    create[ii, q]
    and after (ii in Live and lock[ii])
    and after after (ii.administrativeState = LOCKED and unlock[ii])
    and after after after (ii.administrativeState = UNLOCKED and consume[ii, amt])
    and after after after after (ii.fillState = EMPTY and delete[ii])
    and after after after after after (ii in Retired and ii not in Live)
} for 6 but 3 Scalar

// Split then the husk (emptied original) is Deletable while the split-off lives on.
run unit_lc_splitThenDeleteHusk {
  some o, n: InventoryItem, g: Quantity |
    no o.degradedQty and split[o, n, g, none]                  // split off the whole good portion → husk
    and after (o.fillState = EMPTY and n in Live and delete[o])
    and after after (o in Retired and n in Live)
} for 6 but 3 Scalar
