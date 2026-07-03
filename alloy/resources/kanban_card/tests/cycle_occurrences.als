module resources/kanban_card/tests/cycle_occurrences

open resources/kanban_card/cycle_occurrences
open resources/kanban_card/kanban_card

/*
 * Suite for the CardCycle occurrence log (DT-015 Phase A bones). Premises via the P1 profile in
 * the cone. Card-level readings live HERE for Phase A (they move into the slimmed kanban_card
 * module in Phase B): currentCycleAt / the one-live-cycle theorem need the card's containment
 * facts (Phase B: `currentCycleAt` lives in kanban_card.als). Scope notes: only the PRINT machine
 * remains reified (Phase B retired the op machine) — pins are 5 State / 8 Signal / 8 Transition /
 * 1 StateMachine; `5 Int` is REQUIRED — the region ranks reach 8, which overflows 4-bit Int.
 */

// ── witnesses ───────────────────────────────────────────────────────────────────────────────────
// Genesis births the cycle demanding: REQUESTING, live, empty-handed.
run unit_cyc_genesisBirths {
  some o: RequestOcc | committed[o]
    and statusAt[o.cycle, o.tick] = REQUESTING
    and liveCycleAt[o.cycle, o.tick]
    and no stateOfCycleAt[o.cycle, o.tick].sMaterials
} for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

// The demand leg progresses: Request → Accept → StartProcessing, each reading the prior record.
run unit_cyc_demandLegChain {
  some c: CardCycle, r: RequestOcc, a: AcceptOcc, s: StartProcessingOcc | {
    r.cycle = c and a.cycle = c and s.cycle = c
    precedes[r.tick, a.tick] and precedes[a.tick, s.tick]
    committed[r] and committed[a] and committed[s]
    statusAt[c, s.tick] = IN_PROCESS
  }
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

// KQ-S9 in action: with REQUESTED inactive, StartProcessing SKIPS it straight from REQUESTING.
run unit_cyc_skipsInactiveStatus {
  REQUESTED not in LifecycleConfig.active
  some r: RequestOcc, s: StartProcessingOcc | {
    s.cycle = r.cycle and precedes[r.tick, s.tick]
    committed[r] and committed[s] and s.pre.sStatus = REQUESTING
  }
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

// Shelve — the sanctioned backward step: REQUESTED → REQUESTING.
run unit_cyc_shelveStepsBack {
  some a: AcceptOcc, sh: ShelveOcc | {
    sh.cycle = a.cycle and precedes[a.tick, sh.tick]
    committed[a] and committed[sh]
    statusAt[sh.cycle, sh.tick] = REQUESTING
  }
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

// Receive attaches materials (KD12 accrual).
run unit_cyc_receiveAttachesMaterials {
  some o: ReceiveOcc | committed[o] and some o.materials
    and o.materials in stateOfCycleAt[o.cycle, o.tick].sMaterials
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 2 InventoryItem expect 1

// ROLLOVER closes the predecessor: the successor's genesis reads c1 back as COMPLETED, not live.
run unit_cyc_rolloverCompletesPredecessor {
  some disj c1, c2: CardCycle, r2: RequestOcc | {
    c2.precededBy = c1 and r2.cycle = c2 and committed[r2]
    completedAt[c1, r2.tick] and not liveCycleAt[c1, r2.tick] and liveCycleAt[c2, r2.tick]
  }
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

// WITHDRAW closes the cycle: read back as ABANDONED, not live (the tombstone).
run unit_cyc_withdrawAbandons {
  some w: WithdrawOcc | committed[w]
    and abandonedAt[w.cycle, w.tick] and not liveCycleAt[w.cycle, w.tick]
} for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

// ── reason-precise refusals ─────────────────────────────────────────────────────────────────────
// A backward jump (Accept after IN_PROCESS) is refused with exactly RBackward.
run unit_cyc_backwardRefused {
  some o: AcceptOcc | refusedAtAdmission[o] and o.admission.because = RBackward
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

// Skipping an ACTIVE status is refused with exactly RSkippedActive.
run unit_cyc_skippedActiveRefused {
  some o: StartProcessingOcc | refusedAtAdmission[o] and o.admission.because = RSkippedActive
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

// Operating on a withdrawn (closed) cycle is refused with RClosed among the reasons.
run unit_cyc_closedRefused {
  some w: WithdrawOcc, o: UseOcc | {
    committed[w] and o.cycle = w.cycle and precedes[w.tick, o.tick]
    refusedAtAdmission[o] and RClosed in o.admission.because
  }
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

// A second genesis while the predecessor is still open is refused with exactly RCardInCirculation.
run unit_cyc_genesisWhileOpenRefused {
  some o: RequestOcc | refusedAtAdmission[o] and o.admission.because = RCardInCirculation
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

// Shelve from a status other than REQUESTED is refused with exactly RNotRequested.
run unit_cyc_shelveWrongSourceRefused {
  some o: ShelveOcc | refusedAtAdmission[o] and o.admission.because = RNotRequested
} for 6 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      2 CardCycle, 1 KanbanCard, 0 InventoryItem expect 1

// ── theorems (check; UNSAT = holds) ─────────────────────────────────────────────────────────────
// ≤ 1 live cycle per card — DERIVED from the genesis guard + the chain facts (was the standing
// LiveCycleIsOpenTail fact; the log makes it a consequence).
assert unit_cyc_oneLiveCyclePerCard {
  all k: KanbanCard, t: Tick | lone currentCycleAt[k, t]
}
check unit_cyc_oneLiveCyclePerCard for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem expect 0

// Forward monotonicity: every committed non-Shelve, non-Withdraw operation strictly advances the
// region order (KD9 — backward motion is impossible outside the sanctioned Shelve).
assert unit_cyc_forwardMonotone {
  all o: cycleForwardOps | (committed[o] and some o.pre) implies
    regionBefore[o.pre.sStatus, o.post.sStatus]
}
check unit_cyc_forwardMonotone for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem expect 0

// The demanding/sourcing legs are empty-handed: any state strictly before FULFILLING carries no
// materials (Receive is the only attacher; Shelve cannot cross back over it).
assert unit_cyc_emptyBeforeFulfilling {
  all o: CycleOcc | (committed[o] and some o.post and regionBefore[o.post.sStatus, FULFILLING])
    implies no o.post.sMaterials
}
check unit_cyc_emptyBeforeFulfilling for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 2 InventoryItem expect 0

// Nothing commits on a closed cycle (terminality of closure).
assert unit_cyc_closureIsTerminal {
  all o: CycleOcc | closedStrictlyBefore[o.cycle, o.tick] implies not committed[o]
}
check unit_cyc_closureIsTerminal for 5 but 5 Int, 3 Scalar, 4 Quantity, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      3 CardCycle, 2 KanbanCard, 0 InventoryItem expect 0
