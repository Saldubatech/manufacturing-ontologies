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
