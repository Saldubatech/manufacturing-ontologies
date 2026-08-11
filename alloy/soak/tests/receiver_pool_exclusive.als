module soak/tests/receiver_pool_exclusive

/*
 * SOAK tier — the §8.5.3 lattice row at its former UNIT scopes, RELOCATED here at DT-023
 * cut 7a. The check discharged in minutes at cuts 5/6; the item-log census (ItemOcc/
 * ItemState riding this cone since the pin re-point) pushed the UNSAT proof past 9h CPU —
 * a cost-class change, not a strength change (assert + scopes verbatim from
 * `receiving/receiver/tests/unit/receiver.als`). Its GENEROUS-scope sibling is
 * `soak_rcv_linePoolExclusive` in receiving_soak.als. `make soak` only; never on the
 * push path. The unit root keeps the SAT lattice companion (anti-vacuity is cheap).
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

assert soak_rcv_linePoolExclusiveUnitScope { linePoolExclusiveWhileLive }
check soak_rcv_linePoolExclusiveUnitScope for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 2 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 1 DemandItem, 0 ProductionDelivery,
      1 CardCycle, 1 KanbanCard, 1 InventoryItem, 2 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation,
      8 Occurrence, 12 EntityId, 7 Tick, 10 Snapshot, 2 Note expect 0
