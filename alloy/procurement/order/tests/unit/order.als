module procurement/order/tests/unit/order

open procurement/order/order_implementation
open procurement/order/order_contracts
open operations/demand/demand_mock                            // demand as CONTRACT (DT-017 — the FIRST consumer of demand_mock)
open reference_data/item/item_mock                            // lower layers as CONTRACT
open reference_data/business_affiliate/business_affiliate_mock
open resources/processing_network/processing_network_mock
open resources/kanban_card/kanban_card_mock

/*
 * UNIT suite for the order module (DT-018; TWO subjects on the spine). Every demand-side state
 * this suite needs rides the demand MOCK (contract only — no demand chaining/effects), so
 * demand records are cheap to instantiate at whatever status a scenario needs. Machine pins:
 * the PRINT machine (5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard) rides the
 * kanban types open; 5 Int. NB `for N` silently caps the TOTALS of the ABSTRACT parents —
 * Snapshot (records across ALL subjects) and the occurrence pool: heavy traces pin Snapshot,
 * Tick, and EntityId explicitly (the 2026-07-06 folklore).
 * The sReceived accumulate reading is discharged in the DEDICATED root (order_received.als).
 */

// ── CONTRACT DISCHARGE (check; UNSAT = the law holds of the implementation) ─────────────────────
assert unit_ord_contract_frozenOutsideDraft { frozenOutsideDraft }
check unit_ord_contract_frozenOutsideDraft for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station expect 0

assert unit_ord_contract_demandIndivisible { demandIndivisible }
check unit_ord_contract_demandIndivisible for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station expect 0

assert unit_ord_contract_attachRequiresReleased { attachRequiresReleased }
check unit_ord_contract_attachRequiresReleased for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station expect 0

assert unit_ord_contract_attachItemAgrees { attachItemAgrees }
check unit_ord_contract_attachItemAgrees for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station expect 0

assert unit_ord_contract_submitRequiresStarted { submitRequiresStarted }
check unit_ord_contract_submitRequiresStarted for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station expect 0

assert unit_ord_contract_receiptAccrues { receiptAccrues }
check unit_ord_contract_receiptAccrues for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station, 8 Quantity expect 0

assert unit_ord_contract_lineClosureByAct { lineClosureByAct }
check unit_ord_contract_lineClosureByAct for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station expect 0

assert unit_ord_contract_closeRequiresSettled { closeRequiresSettled }
check unit_ord_contract_closeRequiresSettled for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station expect 0

assert unit_ord_contract_supplierBindingFrozen { supplierBindingFrozen }
check unit_ord_contract_supplierBindingFrozen for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station expect 0

assert unit_ord_contract_orderTerminalClosure { orderTerminalClosure }
check unit_ord_contract_orderTerminalClosure for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station expect 0

assert unit_ord_contract_lineDescriptorFrozen { lineDescriptorFrozen }
check unit_ord_contract_lineDescriptorFrozen for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 3 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      3 ItemDescriptor expect 0

// ── SAT witnesses — the §2 scenarios ────────────────────────────────────────────────────────────
// Smoke/genesis: Create births DRAFT.
run unit_ord_createDraft {
  some o: CreateOrderOcc | committed[o] and orderStatusAt[o.subject, o.tick] = OS_DRAFT
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      7 EntityId expect 1

// Scenario 1 (build and submit, C/OP call-first): Create → AddLine servicing a RELEASED item →
// (the item's StartProduction commits demand-side — the mock supplies IN_PROCESS) → Submit.
run unit_ord_buildAndSubmit {
  some ord: Order, a: AddLineOcc, s: SubmitOcc, d: DemandItem | {
    parentOf[a.subject] = ord
    s.subject = ord
    committed[a] and committed[s]
    resolve[a.demand] = d
    precedes[a.tick, s.tick]
    demandStatusAt[d, a.tick] = DS_RELEASED
    demandStatusAt[d, s.tick] = DS_IN_PROCESS
    orderStatusAt[ord, s.tick] = OS_SUBMITTED
    d in servicedOf[ord, s.tick]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 Tick, 10 EntityId, 10 Snapshot expect 1

// Scenario 3 (acknowledgment, WAIVED flavor): the auto-confirm fires after Submit; the CONFIRMED
// derived reading holds (transient — a reading, not a transition).
run unit_ord_waivedConfirm {
  some ord: Order, k: RecordAcknowledgmentOcc | {
    parentOf[k.subject] = ord
    committed[k]
    k.confirmation.disposition = DISP_WAIVED
    confirmedReadingAt[ord, k.tick]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 Tick, 9 EntityId, 10 Snapshot expect 1

// Scenario 4a (the C/NOTIF accrual, settled): a demand-side accrual is posted to the holding
// line; the quiescence law holds WITH REAL CONTENT and the RECEIVING reading flips.
run unit_ord_receiptSettles {
  some rp: RecordProductionOcc, rr: RecordReceiptOcc, t: Tick | {
    committed[rp] and committed[rr]
    rr.subject in holdingLineOf[rp.subject, t]
    precedes[rp.tick, rr.tick] and notAfter[rr.tick, t]
    receiptsSettledAt[t]
    receivingReadingAt[parentOf[rr.subject], t]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 Tick, 10 EntityId, 10 Snapshot, 4 Quantity expect 1

// Scenario 4b (the C/NOTIF MISSED-NOTIFICATION WINDOW — must be LEGAL): an accrual committed,
// no posting yet, the quiescence law FALSE. The emitter cannot fix it; the listener/probe will.
run unit_ord_missedNotificationLegal {
  some rp: RecordProductionOcc, t: Tick | {
    committed[rp] and notAfter[rp.tick, t]
    some holdingLineOf[rp.subject, t]
    no rr: RecordReceiptOcc | committed[rr]
    not receiptsSettledAt[t]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 Tick, 10 EntityId, 10 Snapshot expect 1

// Scenario 4c (the SELF-HEAL trace): the missed window is later repaired by the SAME kind (the
// probe's re-drive / manual posting) and quiescence is restored.
run unit_ord_selfHealRestores {
  some rp: RecordProductionOcc, rr: RecordReceiptOcc, t1, t2: Tick | {
    committed[rp] and committed[rr]
    rr.subject in holdingLineOf[rp.subject, t2]
    notAfter[rp.tick, t1] and precedes[t1, rr.tick] and notAfter[rr.tick, t2]
    some holdingLineOf[rp.subject, t1]
    not receiptsSettledAt[t1]
    receiptsSettledAt[t2]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      10 Tick, 10 EntityId, 10 Snapshot, 4 Quantity expect 1

// Scenario 5 (close short): a line closed BY ACT with open ≠ 0 (the derived "short" reading),
// then the order closes.
run unit_ord_closeShort {
  some ord: Order, cl: CloseLineOcc, c: CloseOrderOcc | {
    parentOf[cl.subject] = ord and c.subject = ord
    committed[cl] and committed[c]
    precedes[cl.tick, c.tick]
    some openOf[cl.subject, cl.tick]              // short: the open reading is non-zero at the close tick
    orderStatusAt[ord, c.tick] = OS_CLOSED
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 Tick, 9 EntityId, 10 Snapshot, 4 Quantity expect 1

// Scenario 6 (cancel, DRAFT only): plain abandonment while composing.
run unit_ord_cancelDraft {
  some c: CancelOrderOcc | committed[c] and orderStatusAt[c.subject, c.tick] = OS_CANCELED
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      7 EntityId expect 1

// Scenario 6 corollary: THE HOLD DIES WITH THE ORDER — after Cancel, the serviced item is back
// in the queue (holdingLineOf empty) with NO line-by-line choreography; a NEW order may attach
// it (the guard's held-scan sees no live-order hold).
run unit_ord_cancelReturnsToQueue {
  some c: CancelOrderOcc, d: DemandItem, l: OrderLine | {
    committed[c]
    parentOf[l] = c.subject
    d in servicedAt[l, c.tick]                       // the line still RECORDS the servicing…
    no holdingLineOf[d, c.tick]                      // …but the HOLD is gone with the order
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 Tick, 10 EntityId, 10 Snapshot expect 1

// The copy-freeze arc (MP 2026-07-08): the descriptor lands at genesis and survives a later
// mutation untouched — the frozen denotation lives on the line's OWN log.
run unit_ord_descriptorCapturedFrozen {
  some a: AddLineOcc, u: UpdateLineOcc | {
    committed[a] and committed[u]
    a.subject = u.subject and precedes[a.tick, u.tick]
    some a.itemData
    lineStateAt[a.subject, u.tick].sItemData = a.itemData
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 ItemDescriptor, 9 Tick, 9 EntityId, 9 Snapshot, 3 Quantity expect 1

// The F8 arc: choose → override → ResetToSupplier discards the overrides, keeps the identity.
run unit_ord_resetToSupplier {
  some r: ResetToSupplierOcc | {
    committed[r]
    some oPre[r].sSupplier.overrides
    no oPost[r].sSupplier.overrides
    oPost[r].sSupplier.reference = oPre[r].sSupplier.reference
    oPost[r].sSupplier.name = oPre[r].sSupplier.name
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      8 EntityId, 8 Snapshot, 3 SupplierBinding expect 1

// ── refusal witnesses — one per Reason, reason-PRECISE (because = exactly the set) ──────────────
run unit_ord_orderStartedRefused {
  some o: CreateOrderOcc | refusedAtAdmission[o] and o.admission.because = ROrderStarted
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      7 EntityId expect 1

run unit_ord_orderClosedRefused {
  some o: UpdateSupplierOcc | refusedAtAdmission[o] and o.admission.because = ROrderClosed
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      7 EntityId expect 1

run unit_ord_lineStartedRefused {
  some o: AddLineOcc | refusedAtAdmission[o] and o.admission.because = RLineStarted
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      8 EntityId expect 1

run unit_ord_lineClosedRefused {
  some o: UpdateLineOcc | refusedAtAdmission[o] and o.admission.because = RLineClosed
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      8 EntityId, 8 Snapshot expect 1

run unit_ord_frozenRefused {
  some o: AddLineOcc | refusedAtAdmission[o] and o.admission.because = RFrozen
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 2 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 EntityId, 8 Snapshot expect 1

run unit_ord_badStateRefused {
  some o: CancelOrderOcc | refusedAtAdmission[o] and o.admission.because = RBadState
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 EntityId, 8 Snapshot expect 1

run unit_ord_noLinesRefused {
  some o: SubmitOcc | refusedAtAdmission[o] and o.admission.because = RNoLines
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      7 EntityId expect 1

run unit_ord_noSupplierRefused {
  some o: SubmitOcc | refusedAtAdmission[o] and o.admission.because = RNoSupplier
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 SupplierName, 9 EntityId, 8 Snapshot expect 1

// PDEV-928 resolution integrity: the vendor handle resolves to a role that is NOT a VENDOR.
run unit_ord_foreignRefRefused {
  some o: CreateOrderOcc | {
    refusedAtAdmission[o] and o.admission.because = RForeignRef
    some r: resolve[o.supplier.reference.vendorRef] & BusinessRole | r.role != VENDOR
  }
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      1 BusinessRole, 1 BusinessAffiliate, 10 EntityId expect 1

run unit_ord_demandHeldRefused {
  some o: AttachDemandOcc | refusedAtAdmission[o] and o.admission.because = RDemandHeld
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 2 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      10 EntityId, 9 Snapshot expect 1

run unit_ord_demandIneligibleRefused {
  some o: AttachDemandOcc | {
    refusedAtAdmission[o] and o.admission.because = RDemandIneligible
    demandStatusAt[resolve[o.demand] & DemandItem, o.tick] = DS_OPEN   // the item is not yet in the queue
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 EntityId, 8 Snapshot expect 1

// C3b (MP ruling 2026-07-10) — the WRONG-ITEM pairing: a RELEASED, live, unheld demand for a
// DIFFERENT item than the line's refuses RDemandIneligible; reason-PRECISE (the status conjunct
// is satisfied, so only the item-agreement fires).
run unit_ord_wrongItemRefused {
  some o: AttachDemandOcc, d: DemandItem | {
    refusedAtAdmission[o] and o.admission.because = RDemandIneligible
    resolve[o.demand] = d
    demandStatusAt[d, o.tick] = DS_RELEASED
    some o.subject.itemRef
    d.itemRef != o.subject.itemRef
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      10 EntityId, 8 Snapshot expect 1

// C3b corollary — the FREE-FORM target: attaching ANY demand (even RELEASED) to a line with no
// itemRef refuses RDemandIneligible. "Documentary only, no demand pairing" (F7 flag 3) is now a
// GUARD, not just prose.
run unit_ord_freeFormAttachRefused {
  some o: AttachDemandOcc, d: DemandItem | {
    refusedAtAdmission[o] and o.admission.because = RDemandIneligible
    resolve[o.demand] = d
    demandStatusAt[d, o.tick] = DS_RELEASED
    freeForm[o.subject]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      10 EntityId, 8 Snapshot expect 1

run unit_ord_notAttachedRefused {
  some o: DetachDemandOcc | refusedAtAdmission[o] and o.admission.because = RNotAttached
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 EntityId, 8 Snapshot expect 1

run unit_ord_linesOpenRefused {
  some o: CloseOrderOcc | refusedAtAdmission[o] and o.admission.because = RLinesOpen
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 EntityId, 8 Snapshot expect 1

run unit_ord_noDemandRefused {
  some o: RecordReceiptOcc | {
    refusedAtAdmission[o] and o.admission.because = RNoDemand
    freeForm[o.subject]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 EntityId, 8 Snapshot, 3 Quantity expect 1

run unit_ord_notTerminalRefused {
  some o: DeleteOrderOcc | refusedAtAdmission[o] and o.admission.because = RNotTerminal
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      7 EntityId expect 1

// The copy-freeze capture refusal (MP 2026-07-08): an ITEM line without its copied descriptor.
run unit_ord_noDescriptorRefused {
  some o: AddLineOcc | {
    refusedAtAdmission[o] and o.admission.because = RNoDescriptor
    some o.subject.itemRef and no o.itemData
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 ItemDescriptor, 9 EntityId, 8 Snapshot expect 1

// ── boundary witnesses (must be LEGAL — never UNSAT) ────────────────────────────────────────────
// A free-form line: documentary only — no item, no demand, no received tracking.
run unit_ord_freeFormLineLegal {
  some a: AddLineOcc | {
    committed[a]
    freeForm[a.subject] and no a.demand
    no lineStateAt[a.subject, a.tick].sDemand
    no qtyMap[lineStateAt[a.subject, a.tick].sReceived]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      8 EntityId, 8 Snapshot expect 1

// PDEV-241: a name-only, UNLINKED supplier is legal from genesis (both handles dangle-free empty).
run unit_ord_nameOnlySupplierLegal {
  some o: CreateOrderOcc | {
    committed[o]
    some o.supplier.name
    no o.supplier.reference.vendorRef and no o.supplier.reference.affiliateRef
  }
} for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 0 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      0 BusinessRole, 0 BusinessAffiliate, 7 EntityId expect 1

// Over-receipt is admissible (the advisory stance): two postings commit; the line stays open.
run unit_ord_overReceiptLegal {
  some disj r1, r2: RecordReceiptOcc | {
    committed[r1] and committed[r2]
    r1.subject = r2.subject
    lineStatusAt[r1.subject, r2.tick] = L_OPEN
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 Tick, 9 EntityId, 10 Snapshot, 5 Quantity expect 1

// R1 one rung up: TWO live lines servicing DIFFERENT DemandItems of the SAME (item, station)
// pair — demandIndivisible constrains ITEMS, not identity pairs.
run unit_ord_samePairDifferentItemsLegal {
  some disj l1, l2: OrderLine, disj d1, d2: DemandItem, t: Tick | {
    d1.itemRef = d2.itemRef and d1.stationRef = d2.stationRef
    liveLineAt[l1, t] and liveLineAt[l2, t]
    d1 in servicedAt[l1, t] and d2 in servicedAt[l2, t]
  }
} for 7 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 Order, 2 OrderLine, 2 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      10 Tick, 14 EntityId, 12 Snapshot expect 1

// The C/OP in-flight intermediate (O2): serviced items already IN_PROCESS, the order still
// DRAFT (no Submit committed) — the crash window is a LEGAL, queryable state.
run unit_ord_inFlightSubmitLegal {
  some ord: Order, d: DemandItem, t: Tick | {
    orderStatusAt[ord, t] = OS_DRAFT
    d in servicedOf[ord, t]
    demandStatusAt[d, t] = DS_IN_PROCESS
    no s: SubmitOcc | committed[s]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 1 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 Tick, 10 EntityId, 10 Snapshot expect 1

// Tombstoned retirement: Delete commits on a CLOSED order; the terminal record persists.
// (Reaching CLOSED needs the FULL arc — Submit refuses RNoLines on a line-less order — so the
// trace is Create → AddLine → Submit → CloseLine → Close → Delete: six occurrences.)
run unit_ord_deleteRetiresTerminal {
  some x: DeleteOrderOcc | {
    committed[x]
    orderStatusAt[x.subject, x.tick] = OS_CLOSED
    orderDeletedAt[x.subject, x.tick]
  }
} for 7 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      10 Tick, 9 EntityId, 10 Snapshot expect 1
