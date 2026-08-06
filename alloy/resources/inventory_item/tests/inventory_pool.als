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
  all p: InventoryPool, t: Tick, ii: heldAt[p, t] | ii.itemRef = p.itemRef
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

// ── custody (§8.5 — DT-020 build cut 2A) ────────────────────────────────────────────────────────
// The custody arc: Hold takes custody (the handle lands on the record), Release ends it;
// membership is framed by both.
run unit_pool_custodyArc {
  some h: PoolHoldOcc, r: PoolReleaseOcc | {
    committed[h] and committed[r]
    h.subject = r.subject and precedes[h.tick, r.tick]
    custodyAt[h.pool, h.tick] = h.holder
    no custodyAt[r.pool, r.tick]
  }
} for 6 but 2 Scalar, 3 Int expect 1

// ONE custody episode per pool (§8.5.1 fresh-per-episode): a re-hold AFTER Release is refused
// with exactly RPoolHeld — the episode is consumed, not merely occupied.
run unit_pool_reHoldRefused {
  some o: PoolHoldOcc | {
    refusedAtAdmission[o] and o.admission.because = RPoolHeld
    some r: PoolReleaseOcc | committed[r] and r.subject = o.subject and precedes[r.tick, o.tick]
  }
} for 7 but 2 Scalar, 3 Int expect 1

// Release without custody is refused.
run unit_pool_releaseUnheldRefused {
  some o: PoolReleaseOcc | refusedAtAdmission[o] and o.admission.because = RPoolNotHeld
} for 6 but 2 Scalar, 3 Int expect 1

// The one-custody-episode THEOREM: never two committed Holds on one pool, over any trace.
assert unit_pool_oneCustodyEpisode {
  all disj a, b: PoolHoldOcc | (committed[a] and committed[b]) implies a.subject != b.subject
}
check unit_pool_oneCustodyEpisode for 6 but 2 Scalar, 3 Int expect 0

// §8.5.2 exemption witness: PoolRemove is LEGAL on a RELEASED pool (membership-truth
// correction — the retirement listener's probe must reach released pools).
run unit_pool_removeOnReleasedLegal {
  some r: PoolReleaseOcc, o: PoolRemoveOcc | {
    committed[r] and committed[o]
    r.subject = o.subject and precedes[r.tick, o.tick]
    no o.pre.custody
  }
} for 7 but 2 Scalar, 3 Int expect 1
