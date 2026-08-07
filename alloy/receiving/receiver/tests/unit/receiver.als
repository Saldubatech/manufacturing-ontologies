module receiving/receiver/tests/unit/receiver

open receiving/receiver/receiver_implementation
open receiving/receiver/receiver_contracts
open operations/demand/demand_mock                            // demand as CONTRACT (DT-017)
open procurement/order/order_mock                             // order as CONTRACT (the OrderLine targets)
open reference_data/item/item_mock                            // lower layers as CONTRACT
open reference_data/business_affiliate/business_affiliate_mock
open resources/processing_network/processing_network_mock
open resources/kanban_card/kanban_card_mock
open resources/inventory_item/inventory_item_mock

/*
 * UNIT suite for the receiving module (DT-020 cut 4; THREE subjects on the spine). Every
 * peer state this suite needs rides the peers' MOCKS (contracts only — no peer machinery),
 * so demand/cycle/order records are cheap to instantiate at whatever status a scenario
 * needs; the POOL rides the real inventory_pool (single-file module, part of the types
 * cone — the kanban precedent). Machine pins: the PRINT machine (5 State, 8 Signal,
 * 8 Transition, 1 StateMachine, 0 Guard) rides the kanban types open; 5 Int. NB `for N`
 * silently caps the TOTALS of the ABSTRACT parents — Snapshot (records across ALL subjects
 * in this heavy cone) and the occurrence pool: heavy traces pin Snapshot, Tick, and
 * EntityId explicitly (the 2026-07-06 folklore). The order-cone value sigs
 * (SupplierBinding, Confirmation, …) are pinned to 0 wherever no order document
 * participates; attribution `orderLineRef`s may legally DANGLE (soft refs) in scenarios
 * that do not read through them. CHECK SCOPES pin the abstract parents EXPLICITLY, sized
 * from each law's counterexample census (the starved-default lesson: a bare `for 5` caps
 * EntityId below the pinned entity counts and the check passes over starved universes —
 * knowledge-base/pool-lattice-genesis-premise.md §3); light pins for the small-census
 * laws, moderate for the Receive family.
 *
 * The Σ-invariant guards are CASE-WISE (0/1 pre-existing members at attach, 0/1/2
 * allocation keys at Receive — the order_received ceiling applied guard-side): every scope
 * here stays within the exact cases BY DESIGN.
 *
 * The LATTICE ROW (§8.5.3) is NOT dischargeable in this tier: its cross-kind clauses need
 * the peer implementations' EFFECTS (kanban ties sPool to the StartProcessing payload,
 * demand ties sHolding to StartProduction's — provenance the peer CONTRACTS deliberately
 * do not publish, so under the mocks a record may bind a pool no attach act named and the
 * genesis premise cannot reach it). The row discharges in tests/integration/receiver.als
 * (`int_rcv_contract_linePoolExclusive` + its SAT companion) against the real stacks.
 */

// ── CONTRACT DISCHARGE (check; UNSAT = the law holds of the implementation) ─────────────────────
assert unit_rcv_contract_captureWindowFrozen { captureWindowFrozen }
check unit_rcv_contract_captureWindowFrozen for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 2 OrderAttribution, 0 Order, 2 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin, 6 Occurrence, 8 EntityId, 6 Tick, 8 Snapshot expect 0

assert unit_rcv_contract_completeRequiresLinesFinalized { completeRequiresLinesFinalized }
check unit_rcv_contract_completeRequiresLinesFinalized for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin, 6 Occurrence, 8 EntityId, 6 Tick, 8 Snapshot expect 0

assert unit_rcv_contract_capturedFactsFrozen { capturedFactsFrozen }
check unit_rcv_contract_capturedFactsFrozen for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 3 ReceivingLine, 2 OrderAttribution, 0 Order, 2 OrderLine, 0 DemandItem, 1 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin, 8 Occurrence, 10 EntityId, 7 Tick, 10 Snapshot expect 0

assert unit_rcv_contract_receiveSameItemPool { receiveSameItemPool }
check unit_rcv_contract_receiveSameItemPool for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 2 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 2 InventoryItem, 2 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin, 8 Occurrence, 10 EntityId, 7 Tick, 10 Snapshot expect 0

assert unit_rcv_contract_receiveAllocationBounded { receiveAllocationBounded }
check unit_rcv_contract_receiveAllocationBounded for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 2 ReceivingLine, 2 OrderAttribution, 0 Order, 2 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin, 6 Quantity, 8 Occurrence, 10 EntityId, 7 Tick, 10 Snapshot expect 0

assert unit_rcv_contract_actualSetOnce { actualSetOnce }
check unit_rcv_contract_actualSetOnce for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 2 ReceivingLine, 2 OrderAttribution, 0 Order, 2 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin, 6 Occurrence, 8 EntityId, 6 Tick, 8 Snapshot expect 0

assert unit_rcv_contract_deliveriesAppendOnly { deliveriesAppendOnly }
check unit_rcv_contract_deliveriesAppendOnly for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 2 ReceivingLine, 1 OrderAttribution, 0 Order, 1 OrderLine, 0 DemandItem, 2 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin, 6 Occurrence, 8 EntityId, 6 Tick, 8 Snapshot expect 0

assert unit_rcv_contract_lineForwardMonotone { lineForwardMonotone }
check unit_rcv_contract_lineForwardMonotone for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 2 ReceivingLine, 1 OrderAttribution, 0 Order, 1 OrderLine, 0 DemandItem, 1 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin, 6 Occurrence, 8 EntityId, 6 Tick, 8 Snapshot expect 0

assert unit_rcv_contract_receiverTerminalComplete { receiverTerminalComplete }
check unit_rcv_contract_receiverTerminalComplete for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Receiver, 2 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin, 6 Occurrence, 8 EntityId, 6 Tick, 8 Snapshot expect 0

// ── SAT witnesses — the S3prep / S3 arc + refusal surfaces ──────────────────────────────────────
// Smoke/genesis: Create births EDITING.
run unit_rcv_createEditing {
  some o: CreateReceiverOcc | committed[o] and receiverStatusAt[o.subject, o.tick] = RV_EDITING
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 0 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin,
      7 EntityId expect 1

// S3prep-A (from scratch): a blind line — no order linkage, no expectation; the BLIND and
// Undetermined readings hold (the benign, manifest-backed default — §8.4.2).
run unit_rcv_addLineBlind {
  some o: AddReceivingLineOcc | {
    committed[o] and no o.expectedQty and no o.attribution
    rlStatusAt[o.subject, o.tick] = RL_RECEIVING
    lineBlindAt[o.subject, o.tick] and lineUndeterminedAt[o.subject, o.tick]
  }
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin,
      8 EntityId, 8 Tick, 8 Snapshot expect 1

// S3prep-A (from an OrderLine): the line is born WITH its attribution — the same-module
// pairing exercised (AddReceivingLine's attribution arm + the AttachAttribution genesis);
// the ORDER-DRIVEN reading holds.
run unit_rcv_addLineAttributed {
  some o: AddReceivingLineOcc, g: AttachAttributionOcc | {
    committed[o] and committed[g]
    o.attribution = g.subject.eId
    some t: Tick | lineOrderDrivenAt[o.subject, t]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 1 OrderAttribution, 0 Order, 1 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin,
      10 EntityId, 8 Tick, 8 Snapshot, 3 Quantity expect 1

// S3 (the freeze): a full Receive — pool attached (born with the line's act — §8.5.3),
// birth pins stamped, the sActual fan-out committed on the attribution's own log, line
// RECEIVED with the frozen count.
run unit_rcv_receiveFreezes {
  some r: ReceiveLineOcc, x: RecordActualOcc | {
    committed[r] and committed[x]
    some r.pool and some r.birthPins and some r.allocation
    x.subject.eId in r.allocation.Quantity
    rlStatusAt[r.subject, r.tick] = RL_RECEIVED
    some resolve[rlStateAt[r.subject, r.tick].sPool] & InventoryPool
    some t: Tick | some oaStateAt[x.subject, t].sActual
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 1 OrderAttribution, 0 Order, 1 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin,
      12 EntityId, 9 Tick, 10 Snapshot, 4 Quantity expect 1

// §8.3.5: a fully-rejected line — received none, rejected present; births NOTHING and
// attaches NO pool (ReceiveBirthsPooled); still freezes RECEIVED.
run unit_rcv_receiveRejectedOnly {
  some r: ReceiveLineOcc | {
    committed[r] and no r.receivedQty and some r.rejectedQty
    no r.pool and no r.birthPins
    rlStatusAt[r.subject, r.tick] = RL_RECEIVED
  }
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin,
      8 EntityId, 8 Tick, 8 Snapshot, 3 Quantity expect 1

// §8.4.2: the UNEXPECTED classification — no linkage + the operator's explicit off-manifest
// assertion (the exceptional-path input; sStatedQty plays no part).
run unit_rcv_offManifestUnexpected {
  some o: UpdateReceivingLineOcc | {
    committed[o] and some o.offManifest
    lineUnexpectedAt[o.subject, o.tick]
  }
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin,
      8 EntityId, 8 Tick, 8 Snapshot expect 1

// Refusal: a wrong-Item pool is REFUSED with exactly RWrongItem (the same-Item gate — the
// RPoolWrongItem precedent; the pool's classifier may dangle, the mismatch suffices).
run unit_rcv_wrongItemPoolRefused {
  some o: ReceiveLineOcc | refusedAtAdmission[o] and o.admission.because = RWrongItem
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin,
      10 EntityId, 8 Tick, 8 Snapshot expect 1

// Refusal: a pool visibly in use (here: held by ANOTHER line) is REFUSED with exactly
// RPoolInUse — receiving's per-entity-type availability semantics (§8.5.3).
run unit_rcv_poolInUseRefused {
  some o: ReceiveLineOcc | refusedAtAdmission[o] and o.admission.because = RPoolInUse
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 2 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin,
      12 EntityId, 9 Tick, 10 Snapshot expect 1

// Refusal: the Σ-expected attach bound (§8.3.3 d, case n=0) — an attribution whose
// `expected` exceeds the line's cap is REFUSED with exactly ROverAttributed.
run unit_rcv_overAttributedRefused {
  some o: AppendAttributionOcc | refusedAtAdmission[o] and o.admission.because = ROverAttributed
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 1 OrderAttribution, 0 Order, 1 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin,
      10 EntityId, 8 Tick, 8 Snapshot, 4 Quantity expect 1

// Refusal: the Σ-actual Receive bound (§8.3.3 d, one key) — an allocation exceeding the
// accepted count is REFUSED with exactly ROverAllocated.
run unit_rcv_overAllocatedRefused {
  some o: ReceiveLineOcc | refusedAtAdmission[o] and o.admission.because = ROverAllocated
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 1 OrderAttribution, 0 Order, 1 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin,
      12 EntityId, 9 Tick, 10 Snapshot, 5 Quantity expect 1

// §8.1.3: the distribute C/OP's closing append — a committed RecordDelivery lands the PD
// ref in `sDeliveries` on a RECEIVED line (idempotent by set semantics).
run unit_rcv_recordDelivery {
  some o: RecordDeliveryOcc | {
    committed[o]
    o.delivery in rlStateAt[o.subject, o.tick].sDeliveries
    rlStatusAt[o.subject, o.tick] = RL_RECEIVED
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 0 DemandItem, 1 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin,
      10 EntityId, 9 Tick, 9 Snapshot, 3 Quantity expect 1

// §8.2.1/C3: release — Complete([locator]) detaches the pool (custody ends, the derived
// reading; the pool persists) and the line stands DISTRIBUTED.
run unit_rcv_releaseLine {
  some o: ReleaseLineOcc | {
    committed[o]
    rlStatusAt[o.subject, o.tick] = RL_DISTRIBUTED
    some rlPre[o].sPool and no rlStateAt[o.subject, o.tick].sPool
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 1 InventoryItem, 1 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin,
      12 EntityId, 9 Tick, 10 Snapshot, 3 Quantity expect 1

// §8.2: the capture-finalization gate — Complete commits once every child line is
// finalized (the caller's cascade came first); the Receiver stands COMPLETE.
run unit_rcv_completeReceiver {
  some o: CompleteReceiverOcc | {
    committed[o]
    receiverStatusAt[o.subject, o.tick] = RV_COMPLETE
    some linesOfReceiver[o.subject]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin,
      10 EntityId, 9 Tick, 9 Snapshot, 3 Quantity expect 1

// Refusal: Complete against a still-RECEIVING line — exactly RLinesReceiving (the gate).
run unit_rcv_completeRefusedLinesReceiving {
  some o: CompleteReceiverOcc | refusedAtAdmission[o] and o.admission.because = RLinesReceiving
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Receiver, 1 ReceivingLine, 0 OrderAttribution, 0 Order, 0 OrderLine, 0 DemandItem, 0 ProductionDelivery,
      0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierBinding, 0 SupplierName, 0 SupplierData, 0 Confirmation, 0 ItemDescriptorPin,
      8 EntityId, 8 Tick, 8 Snapshot expect 1
