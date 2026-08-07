module receiving/receiver/tests/integration/receiver

open receiving/receiver/receiver_implementation
open receiving/receiver/receiver_contracts
open operations/demand/demand_implementation                 // REAL — the row needs demand's effects
open resources/kanban_card/kanban_card_implementation        // REAL — and kanban's
open reference_data/item/item_mock                           // solver budget: the row reads no item/station
open resources/processing_network/processing_network_mock    //   machinery (the demand_lattice precedent)

// SupplierReference CLOSURE (modeling-conventions §6, handles): this cone carries the shared
// handle through item AND (types-transitively) the order module's bindings; tie it to both
// carrier sets so universes stay tight (the demand-integration precedent, one carrier wider).
fact SupplierReferenceClosed { SupplierReference = itemCarriedSupplierRefs + orderCarriedSupplierRefs }

/*
 * INTEGRATION suite for the receiving module (DT-020 cut 4): the real receiving log composed
 * with the REAL demand + kanban stacks (item/station ride their mocks — solver-budget
 * confinement, the demand_lattice-root precedent: the lattice row reads neither, and the
 * real item stack multiplies solve time for nothing). Gate tier. THIS is where the
 * §8.5.3 LATTICE ROW discharges: the cross-kind clauses are theorems of the guards + the
 * genesis premise ONLY where the peer implementations' EFFECTS tie their records to their
 * attach payloads (kanban: sPool = StartProcessing's pool; demand: sHolding =
 * StartProduction's holding) — the peer CONTRACTS deliberately do not publish that
 * provenance, so the unit tier (peer mocks) cannot see it. The row still joins
 * `guarantees`/the mock in this same change set (the §8.5.3 two-role rule — discharged
 * against the real implementations here).
 *
 * The ORDER module rides this cone TYPES-ONLY (receiving reads no order log); order-cone
 * value sigs are pinned to 0 throughout.
 */

// ── joint loads: the composed stack is satisfiable across all layers ────────────────────────────
run int_rcv_loads {
  some o: ReceiveLineOcc | {
    committed[o] and some o.pool
    some resolve[o.pool] & InventoryPool
    some resolve[rlPre[o].sExpectedItem] & Item
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin,
      12 EntityId, 8 Tick, 10 Snapshot, 3 Quantity expect 1

// ── THE LATTICE ROW (§8.5.3 — scope discipline: 2 of the OWN kind + 1 of each visible kind;
// the lower kinds' same-kind pairs are their own rows' scopes) ──────────────────────────────────
assert int_rcv_contract_linePoolExclusive { linePoolExclusiveWhileLive }
check int_rcv_contract_linePoolExclusive for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 2 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 1 DemandItem, 0 ProductionDelivery,
      1 CardCycle, 1 KanbanCard, 1 InventoryItem, 2 InventoryPool, 1 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin,
      8 Occurrence, 12 EntityId, 7 Tick, 10 Snapshot expect 0

// The SAT companion (anti-vacuity): the genesis premise HOLDS with real multi-kind content —
// a line holding its pool, a LIVE cycle holding a second, a LIVE demand holding a third.
run int_rcv_latticeCompanion {
  receivingPoolGenesis
  some t: Tick, l: ReceivingLine, c: CardCycle, d: DemandItem, p1, p2, p3: InventoryPool | {
    p1 != p2 and p2 != p3 and p1 != p3
    resolve[rlStateAt[l, t].sPool] = p1
    liveCycleAt[c, t] and resolve[stateOfCycleAt[c, t].sPool] = p2
    liveDemandAt[d, t] and resolve[demandStateAt[d, t].sHolding] = p3
  }
} for 10 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 1 DemandItem, 0 ProductionDelivery,
      1 CardCycle, 1 KanbanCard, 1 InventoryItem, 3 InventoryPool, 1 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin,
      16 EntityId, 12 Tick, 14 Snapshot, 4 Quantity, 12 Occurrence expect 1
