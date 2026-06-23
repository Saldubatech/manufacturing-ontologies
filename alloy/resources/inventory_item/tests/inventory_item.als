module resources/inventory_item/tests/inventory_item

open meta/kernel
open meta/values
open meta/x731_state/state
open reference_data/item/item
open resources/inventory_item/inventory_item

/*
 * Unit suite for InventoryItem (DT-004). Opening meta/x731_state brings the region
 * one-sig families into scope: 8 State, 10 Signal, 10 Transition, 3 StateMachine.
 */

// SAT: a coherent inventory item classified by an in-scope Item.
pred unit_inventoryItem_coherent {
  some ii: InventoryItem | some i: Item | resolve[ii.itemRef] = i
}
run unit_inventoryItem_coherent
  for 6 but 8 State, 10 Signal, 10 Transition, 3 StateMachine, 0 Guard, 5 Int

// UNSAT: an inventory item classified by an Item in a different tenant
// (kernel cross-tenant isolation — itemRef is in dataRefs and Item is Scoped).
pred unit_inventoryItem_crossTenantItem {
  some ii: InventoryItem | let i = resolve[ii.itemRef] |
    some i and i in Item and i.tenantId != ii.tenantId
}
run unit_inventoryItem_crossTenantItem
  for 6 but 8 State, 10 Signal, 10 Transition, 3 StateMachine, 0 Guard, 5 Int

// UNSAT: the depletion interlock forbids a zero-quantity item that is not BUSY.
pred unit_inventoryItem_depletionViolation {
  some ii: InventoryItem | ii.actualQuantity.amount = 0 and ii.usageState != BUSY
}
run unit_inventoryItem_depletionViolation
  for 6 but 8 State, 10 Signal, 10 Transition, 3 StateMachine, 0 Guard, 5 Int
