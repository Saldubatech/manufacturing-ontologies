module soak/tests/receiving_soak

/*
 * SOAK tier (DT-022 TQ-5): the receiving freeze + lattice laws at GENEROUS scopes — see
 * kanban_soak.als for the tier's rationale. `make soak` only; never on the push path.
 */

open receiving/receiver/receiver_implementation
open receiving/receiver/receiver_contracts
open operations/demand/demand_mock
open procurement/order/order_mock
open reference_data/item/item_mock
open reference_data/business_affiliate/business_affiliate_mock
open resources/processing_network/processing_network_mock
open resources/kanban_card/kanban_card_mock
open resources/inventory_item/inventory_item_mock
open reference_data/staff/staff_mock

assert soak_rcv_capturedFactsFrozen { capturedFactsFrozen }
check soak_rcv_capturedFactsFrozen for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 Receiver, 4 ReceivingLine, 3 OrderAttribution, 0 Order, 3 OrderLine, 0 DemandItem, 2 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 2 InventoryItem, 2 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin,
      11 Occurrence, 14 EntityId, 9 Tick, 13 Snapshot expect 0

assert soak_rcv_linePoolExclusive { linePoolExclusiveWhileLive }
check soak_rcv_linePoolExclusive for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 2 DemandItem, 0 ProductionDelivery,
      2 CardCycle, 2 KanbanCard, 2 InventoryItem, 3 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin,
      11 Occurrence, 16 EntityId, 9 Tick, 13 Snapshot expect 0
