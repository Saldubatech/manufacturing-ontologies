module resources/inventory_item/tests/inventory_pool

open resources/inventory_item/inventory_pool

/*
 * Suite for the LOG-CARRIED InventoryPool (2026-07-02 re-model; the v1 `var` suite migrated
 * 1:1 — the wrong-Item impossibility guard upgraded to a reason-precise refusal witness, log
 * style). The cone is fully static: no `steps` scopes anymore.
 */

// A pool holding two members exists (two committed adds, read back through the projection).
run unit_pool_loads {
  some p: InventoryPool, t: Tick | #heldAt[p, t] >= 2
} for 6 but 2 Scalar, 3 Int expect 1

// PoolAdd: a committed add makes the item a member as of its own tick.
run unit_pool_add {
  some o: PoolAddOcc | committed[o] and o.item in heldAt[o.pool, o.tick]
} for 6 but 2 Scalar, 3 Int expect 1

// PoolRemove: a committed remove of a held member — gone as of its own tick.
run unit_pool_remove {
  some o: PoolRemoveOcc | committed[o]
    and o.item in o.pre.holds and o.item not in heldAt[o.pool, o.tick]
} for 6 but 2 Scalar, 3 Int expect 1

// Homogeneity at every moment — now a THEOREM derived from the add guard (was an `always` fact).
assert unit_pool_homogeneous {
  all p: InventoryPool, t: Tick, ii: heldAt[p, t] | ii.itemPin.subject = p.itemPin.subject
}
check unit_pool_homogeneous for 6 but 2 Scalar, 3 Int expect 0

// Same-tenant at every moment — the companion theorem (was an `always` fact).
assert unit_pool_sameTenant {
  all p: InventoryPool, t: Tick, ii: heldAt[p, t] | ii.tenantId = p.tenantId
}
check unit_pool_sameTenant for 6 but 2 Scalar, 3 Int expect 0

// A wrong-Item add is REFUSED with exactly RWrongItem (upgrades the old UNSAT impossibility
// guard: the refusal is exhibited with its reason, not merely unrepresentable).
run unit_pool_wrongItemRefused {
  some o: PoolAddOcc | refusedAtAdmission[o] and o.admission.because = RWrongItem
} for 6 but 2 Scalar, 3 Int expect 1

// poolMembershipExclusive (M2b, NEW LAW — DT-020 §8.5.3 / SPEARHEAD-D1 A′-2, MINESWEEPER
// model-deltas M2): at any tick an InventoryItem is held by AT MOST ONE pool. Guard-derived
// THEOREM of the new poolAddViol arm (RHeldElsewhere) below — RED before the arm exists
// (poolAddViol refused RAlreadyMember only for the SAME pool, so two different pools could
// both hold the same item; see the commit body for the RED counterexample).
assert unit_pool_membershipExclusive {
  all ii: InventoryItem, t: Tick | lone { p: InventoryPool | ii in heldAt[p, t] }
}
check unit_pool_membershipExclusive for 6 but 2 Scalar, 3 Int expect 0

// The SAME theorem re-checked with PoolTransferOcc in scope (M2b item 3 — "the exclusivity
// check stays 0 with transfers in scope"): a transfer's paired destination PoolAddOcc is an
// ordinary add and is refused RHeldElsewhere exactly like any other double-hold attempt.
// (Default scope held at 6 — only PoolTransferOcc is pinned up — bumping the overall default
// to 7 inflates every unbound abstract family in the cone and blows up solve time.)
check unit_pool_membershipExclusive for 6 but 2 Scalar, 3 Int, 1 PoolTransferOcc expect 0

// ── PoolTransferOcc (M2b, NEW KIND — DT-020 §8.5.3 / SPEARHEAD-D1 A′-2): the ONE kind that
// moves an item between pools. RED before poolTransferViol's real arms exist: the guard is a
// STUB (`none`) at first commit of this file — refusedAtAdmission is UNSAT for every
// PoolTransferOcc, so the two refusal witnesses below are UNSAT (RED); see the commit body.

// A committed transfer moves the item: gone from the source, present in the destination as of
// the paired add's tick.
run unit_pool_transfer {
  some o: PoolTransferOcc | committed[o]
    and o.item not in heldAt[o.pool, o.tick]
    and (some a: PoolAddOcc | committed[a] and a.pool = o.to and a.item = o.item and precedes[o.tick, a.tick]
           and o.item in heldAt[o.to, a.tick])
} for 6 but 2 Scalar, 3 Int expect 1

// A transfer into a pool of a DIFFERENT Item is refused with exactly RWrongItem (judged at the
// DESTINATION — the pool-vs-pool item agreement, DT-020 §8.5.3).
run unit_pool_transferWrongItemRefused {
  some o: PoolTransferOcc | refusedAtAdmission[o] and o.admission.because = RWrongItem
} for 6 but 2 Scalar, 3 Int expect 1

// A transfer of an item the SOURCE pool does not currently hold is refused with exactly
// RNotMember.
run unit_pool_transferNotMemberRefused {
  some o: PoolTransferOcc | refusedAtAdmission[o] and o.admission.because = RNotMember
} for 6 but 2 Scalar, 3 Int expect 1

// A same-pool transfer (`to` = `from`) is refused with exactly RSameTarget.
run unit_pool_transferSameTargetRefused {
  some o: PoolTransferOcc | refusedAtAdmission[o] and o.admission.because = RSameTarget
} for 6 but 2 Scalar, 3 Int expect 1

// ── splitInPool (M2b composite, a DERIVED predicate — not a kind): a split's new sibling lands
// in the same pool that held the split target.
run unit_pool_splitInPool {
  some s: SplitOcc, a: PoolAddOcc | splitInPool[s, a]
} for 7 but 2 Scalar, 3 Int expect 1
