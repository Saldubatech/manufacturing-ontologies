module soak/tests/demand_soak

/*
 * SOAK tier (DT-022 TQ-5): the demand lattice/provenance laws at GENEROUS scopes — see
 * kanban_soak.als for the tier's rationale. `make soak` only; never on the push path.
 */

open operations/demand/demand_implementation
open operations/demand/demand_contracts
open reference_data/item/item_mock
open resources/processing_network/processing_network_mock
open resources/kanban_card/kanban_card_mock

assert soak_dem_holdingProvenance { holdingProvenance }
check soak_dem_holdingProvenance for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 DemandItem, 1 CardCycle, 2 KanbanCard, 1 InventoryItem, 3 InventoryPool,
      11 Occurrence, 14 EntityId, 9 Tick, 11 Snapshot expect 0

assert soak_dem_holdingExclusive { holdingExclusiveWhileLive }
check soak_dem_holdingExclusive for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 DemandItem, 2 CardCycle, 2 KanbanCard, 1 InventoryItem, 3 InventoryPool,
      11 Occurrence, 14 EntityId, 9 Tick, 11 Snapshot expect 0
