module resources/inventory_item/legacy/tests/lifecycle

open resources/inventory_item/legacy/operations

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
               and replenish[ii, delta, none, none])
    and after after (ii in Live and ii.fillState != EMPTY)    // revived
} for 6 but 3 Scalar expect 1

// Consume-to-zero NEVER retires the item — it stays Live (distinguishes deplete from Delete).
assert unit_lc_depletionDoesNotRetire {
  always all ii: InventoryItem, q: Quantity |
    (ii in Live and consume[ii, q]) implies after (ii in Live and ii not in Retired)
}
check unit_lc_depletionDoesNotRetire for 6 but 3 Scalar expect 0

// Delete IS terminal: once retired, an item is never Live again (D9/G5 non-reusability across time).
assert unit_lc_deleteTerminal {
  always all ii: InventoryItem | ii in Retired implies always ii not in Live
}
check unit_lc_deleteTerminal for 6 but 3 Scalar expect 0

// A deleted item's license plate is never taken by any other item (immutable + global uniqueness).
assert unit_lc_lpnNeverReused {
  always all disj a, b: InventoryItem | a.licensePlate != b.licensePlate
}
check unit_lc_lpnNeverReused for 6 but 3 Scalar expect 0

// ── D16 Fill: born OPEN; SEALED is operator-asserted and RE-ENTERABLE ───────────────────────

// Born OPEN: a freshly created item is OPEN, never SEALED (creation presumes no operator intent —
// the D15 born-FULL rule is retired).
assert unit_lc_bornOpen {
  always all ii: InventoryItem, q: Quantity | create[ii, q, none] implies after ii.fillState = OPEN
}
check unit_lc_bornOpen for 6 but 3 Scalar expect 0

// A quantity-changing op always breaks the seal: SEALED --consume--> OPEN (or EMPTY to zero).
assert unit_lc_quantityChangeBreaksSeal {
  always all ii: InventoryItem, q: Quantity |
    (ii in Live and ii.fillState = SEALED and consume[ii, q]) implies after (ii.fillState != SEALED)
}
check unit_lc_quantityChangeBreaksSeal for 6 but 3 Scalar expect 0

// SEALED is RE-ENTERABLE (the D15 "never re-entered" rule is gone): seal → unseal → seal again.
run unit_lc_sealUnsealReseal {
  some ii: InventoryItem |
    ii.fillState = OPEN and seal[ii]
    and after (ii.fillState = SEALED and unseal[ii])
    and after after (ii.fillState = OPEN and seal[ii])
    and after after after (ii.fillState = SEALED)
} for 6 but 3 Scalar expect 1

// Full fill cycle: OPEN → (seal) SEALED → (consume) OPEN → (consume-to-zero) EMPTY → (replenish) OPEN.
run unit_lc_fillCycle {
  some ii: InventoryItem, a1, a2, r: Quantity |
    ii.fillState = OPEN and seal[ii]
    and after (ii.fillState = SEALED and consume[ii, a1])
    and after after (ii.fillState = OPEN and consume[ii, a2])
    and after after after (ii.fillState = EMPTY and replenish[ii, r, none, none])
    and after after after after (ii.fillState = OPEN)
} for 6 but 3 Scalar expect 1

// D17: expiration never increases — Merge/Replenish can only shorten it; all other ops preserve it.
assert unit_lc_expirationNeverIncreases {
  always (someOp implies all ii: InventoryItem |
    (ii in Live and ii in Live' and some ii.expirationDate and some ii.expirationDate')
      implies (ii.expirationDate' = ii.expirationDate or ii.expirationDate' < ii.expirationDate))
}
check unit_lc_expirationNeverIncreases for 6 but 3 Scalar expect 0

// ── representative end-to-end lifecycle (expect SAT) ──────────────────────────────────────

// Create → Lock → Unlock → Consume-to-zero → Delete: a full birth-to-retirement path.
run unit_lc_fullLifecycle {
  some ii: InventoryItem, q, amt: Quantity |
    create[ii, q, none]
    and after (ii in Live and lock[ii])
    and after after (ii.administrativeState = LOCKED and unlock[ii])
    and after after after (ii.administrativeState = UNLOCKED and consume[ii, amt])
    and after after after after (ii.fillState = EMPTY and delete[ii])
    and after after after after after (ii in Retired and ii not in Live)
} for 6 but 3 Scalar expect 1

// Split then the husk (emptied original) is Deletable while the split-off lives on.
run unit_lc_splitThenDeleteHusk {
  some o, n: InventoryItem, g: Quantity |
    no o.degradedQty and split[o, n, g, none]                  // split off the whole good portion → husk
    and after (o.fillState = EMPTY and n in Live and delete[o])
    and after after (o in Retired and n in Live)
} for 6 but 3 Scalar expect 1
