module soak/tests/order_soak

/*
 * SOAK tier (DT-022 TQ-5): the order freeze family at GENEROUS scopes — see
 * kanban_soak.als for the tier's rationale. NB the gate's older order checks ride `for 5`
 * DEFAULTS for the abstract parents (EntityId/Tick/Snapshot) — precisely the census this
 * tier exists to widen. `make soak` only; never on the push path.
 */

open procurement/order/order_implementation
open procurement/order/order_contracts
open operations/demand/demand_mock
open reference_data/item/item_mock
open reference_data/business_affiliate/business_affiliate_mock
open resources/processing_network/processing_network_mock
open resources/kanban_card/kanban_card_mock
open reference_data/staff/staff_mock

assert soak_ord_frozenOutsideDraft { frozenOutsideDraft }
check soak_ord_frozenOutsideDraft for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 Order, 4 OrderLine, 3 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 11 Occurrence, 14 EntityId, 9 Tick, 13 Snapshot, 2 Note expect 0

assert soak_ord_supplierBindingFrozen { supplierBindingFrozen }
check soak_ord_supplierBindingFrozen for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 Order, 4 OrderLine, 3 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 11 Occurrence, 14 EntityId, 9 Tick, 13 Snapshot, 2 Note expect 0

assert soak_ord_headerDetailFrozen { headerDetailFrozen }
check soak_ord_headerDetailFrozen for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 Order, 3 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      3 StaffMember, 11 Occurrence, 14 EntityId, 9 Tick, 13 Snapshot, 2 Note expect 0

assert soak_ord_terminalClosure { orderTerminalClosure }
check soak_ord_terminalClosure for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 Order, 4 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 StaffMember, 11 Occurrence, 14 EntityId, 9 Tick, 13 Snapshot, 2 Note expect 0

// CREATED-ONLY SLICE (DT-023 Q-D / DT-024, closing pass 7c): reference-data version
// dynamics are proven WIDE in soak/tests/reference_data_dynamics — this root reads
// reference data only through the pin/liveness API, so each subject carries exactly its
// Create and no Update/Delete atoms inflate the census (the lemma-then-slice retune).
fact CreatedOnlySlice {
  ItemOcc in CreateItemOcc
  BaOcc in CreateBaOcc
  StaffOcc in CreateStaffOcc
}
