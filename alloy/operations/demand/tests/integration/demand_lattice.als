module operations/demand/tests/integration/demand_lattice

open operations/demand/demand_implementation
open operations/demand/demand_contracts
open resources/kanban_card/kanban_card_implementation   // REAL — the row needs kanban's effects
open reference_data/item/item_mock                      // solver budget: the row reads no item/station
open resources/processing_network/processing_network_mock

/*
 * THE DEDICATED demand-lattice root (§8.5.3, DT-020 cut 4 — the order_received/demand_reset
 * solver-budget-confinement precedent): the demand LATTICE ROW's discharge tier. The row
 * (`holdingExclusiveWhileLive`) is a guard-and-genesis-derived theorem whose cross-kind
 * clause needs KANBAN'S REAL EFFECTS (`sPool` tied to the StartProcessing payload —
 * provenance the kanban contract deliberately does not publish, so the kanban MOCK cannot
 * discharge it). Item and station ride their MOCKS: the row reads neither, and the real
 * item stack's machinery multiplies solve time for nothing (measured: the full
 * demand-integration cone ground >5 min on this check; this root solves it in seconds).
 * The composed-stack witnesses stay in tests/integration/demand.als.
 *
 * Scope discipline: 2 of the OWN kind + 1 of each visible kind (the cycle-pair row is
 * kanban's own), explicit abstract-parent pins (a starved default EntityId cap would pass
 * vacuously — knowledge-base/pool-lattice-genesis-premise.md).
 */

assert int_dem_contract_holdingExclusive { holdingExclusiveWhileLive }
check int_dem_contract_holdingExclusive for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 DemandItem, 1 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 InventoryPool,
      8 Occurrence, 10 EntityId, 7 Tick, 8 Snapshot expect 0

// The SAT companion (anti-vacuity): the genesis premise HOLDS with real content — a LIVE
// demand holding its pool and a LIVE cycle holding a distinct one.
run int_dem_latticeCompanion {
  demandPoolGenesis
  some t: Tick, d: DemandItem, c: CardCycle, disj p1, p2: InventoryPool | {
    liveDemandAt[d, t] and resolve[demandStateAt[d, t].sHolding] = p1
    liveCycleAt[c, t] and resolve[stateOfCycleAt[c, t].sPool] = p2
  }
} for 8 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 DemandItem, 2 CardCycle, 1 KanbanCard, 0 InventoryItem, 2 InventoryPool,
      10 EntityId, 8 Tick, 10 Snapshot, 8 Occurrence expect 1
