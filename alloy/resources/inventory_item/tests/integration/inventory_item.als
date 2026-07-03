module resources/inventory_item/tests/integration/inventory_item

open resources/inventory_item/inventory_item_implementation
open resources/inventory_item/inventory_item_contracts
open reference_data/item/item_implementation       // the LOWER LAYER for real (DT-017 two-layer PoC)

/*
 * INTEGRATION suite for the InventoryItem module (DT-017): the real II log composed with the
 * REAL item stack (supplies, supplier chain, UoM laws as implementation facts, not assumptions).
 * This is the gate/soak tier — the unit tier (tests/unit/) runs the same implementation against
 * item's MOCK for the dev loop. Kept deliberately small: a joint loads witness (the composed
 * universe is satisfiable), a cross-layer resolution witness through the supplier chain, and a
 * re-discharge of two contract laws on the composed stack.
 */

// ── joint loads (guard-rail: the composed stack is satisfiable, no vacuity) ──────────────────────
// A committed Create on an item whose classifier resolves to a TRACKED Item under the full real
// item laws — the composition actually loads.
run int_ii_loads {
  some o: CreateOcc | committed[o]
    and (let i = resolve[o.target.itemRef] | some i and some (i & Item).uom)
    and liveAt[o.target, o.tick]
} for 5 but 3 Scalar, 5 Int expect 1

// ── cross-layer composition: the deep supplier chain resolves in one universe with a live log ───
run int_ii_supplyChainLoads {
  some ii: InventoryItem, i: Item, s: ItemSupply | {
    resolve[ii.itemRef] = i
    resolve[i.defaultSupply] = s
    some resolve[s.supplier.vendorRef]
    some o: CreateOcc | committed[o] and o.target = ii
  }
} for 6 but 3 Scalar, 5 Int, 9 EntityId expect 1

// ── contract re-discharge on the composed stack (UNSAT = holds with the real lower layer) ───────
assert int_ii_contract_stateFunction { stateIsFunctionOnceStarted }
check int_ii_contract_stateFunction for 5 but 3 Scalar, 5 Int expect 0

assert int_ii_contract_closureIsTerminal { closureIsTerminal }
check int_ii_contract_closureIsTerminal for 5 but 3 Scalar, 5 Int expect 0
