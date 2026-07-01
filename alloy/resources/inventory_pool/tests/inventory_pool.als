module resources/inventory_pool/tests/inventory_pool

open resources/inventory_pool/inventory_pool

/*
 * v1 sanity for InventoryPool: a homogeneous pool exists, add/remove behave, membership is homogeneous,
 * and a wrong-Item add is impossible. `items` is `var`, so temporal commands carry a `steps` scope.
 */

// A pool with two members exists (homogeneity is enforced by fact).
run unit_pool_loads {
  some p: InventoryPool | #p.items >= 2
} for 6 but 2 Scalar, 1 steps expect 1

// addItem: a non-member of the pool's Item can be added → it becomes a member next state.
run unit_pool_add {
  some p: InventoryPool, ii: InventoryItem | ii not in p.items and addItem[p, ii] and ii in p.items'
} for 6 but 2 Scalar, 2 steps expect 1

// removeItem: a member can be removed → it is absent next state.
run unit_pool_remove {
  some p: InventoryPool, ii: InventoryItem | removeItem[p, ii] and ii not in p.items'
} for 6 but 2 Scalar, 2 steps expect 1

// Homogeneity holds in every state: a member's Item is the pool's Item.
assert unit_pool_homogeneous {
  always all p: InventoryPool, ii: p.items | ii.itemRef = p.itemRef
}
check unit_pool_homogeneous for 6 but 2 Scalar, 3 steps expect 0

// A wrong-Item add is impossible — the guard forbids adding an item of a different Item.
run unit_pool_wrongItemImpossible {
  some p: InventoryPool, ii: InventoryItem | ii.itemRef != p.itemRef and addItem[p, ii]
} for 6 but 2 Scalar, 2 steps expect 0
