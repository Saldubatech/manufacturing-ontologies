module resources/kanban_card/cycle_occurrences

/*
 * The CardCycle OCCURRENCE LOG (DT-015 Phase A — built ALONGSIDE the standing structural model):
 * one occurrence kind per OPERATION (terminology canon: an occurrence records an Operation
 * invocation; the EVENT is the committed pre→post change; projections are the notifications).
 *
 * The lifecycle discipline (KD9/KQ-S1/KQ-S9) is the ADMISSION GUARD: the canonical region order
 * (cycle_state.als) + a reified per-deployment configuration (`LifecycleConfig.active` — the
 * industry survey's control-cycle precedent): a forward operation may SKIP only INACTIVE statuses.
 * TWO sanctioned backward operations: `Shelve` (REQUESTED → REQUESTING) and `ProductionFailure`
 * (IN_PROCESS → REQUESTING — DT-016 R8, amended 2026-07-06: a production run completed without allocating this cycle
 * any inventory; the cycle re-enters the waiting queue REQUESTING, attachable by a new DemandItem). Reason-precise
 * witnessing throughout. R7 (DT-016): the cycle QUANTITY IS FIXED AT GENESIS — `sQuantityOverride`
 * is written by `RequestOcc` only and framed by every other effect (theorem
 * unit_cyc_quantityFixedAtGenesis).
 *
 * CLOSURE (the SQ-8 dissolution, pending the Q3/Q4 re-evaluation): a cycle is closed by a
 * committed `WithdrawOcc` (read back: ABANDONED) or by its SUCCESSOR's committed `RequestOcc`
 * (rollover — read back: COMPLETED). Genesis: `RequestOcc` births the cycle (KC-MH-10) and
 * requires the predecessor cycle closed — so "≤ 1 live cycle per card" becomes a theorem.
 *
 * Cycle occurrences share the ONE causal Tick order with IIOcc/PoolOcc — the composition seam
 * DT-014 needs (card events as collatable demand signals for DemandItem).
 */

open meta/profiles/domain_log                 // PROFILE (DT-012): the log anatomy (StatefulAction, Tick, verdicts)
open resources/kanban_card/cycle_state        // CycleState + region order (+ card_cycle, inventory_pool transitively)

// ── per-deployment lifecycle configuration (KQ-S9 — reified, not hard-coded) ────────────────────
/** LifecycleConfig — which core statuses this deployment uses; inactive ones are SKIPPED. */
one sig LifecycleConfig { active: set KanbanCardStatus }
fact ConfigWellFormed { LifecycleConfig.active in (KanbanCardStatus - AVAILABLE) }

// ── the kinds — one per Operation (`<Operation>Occ`) ────────────────────────────────────────────
/** CycleOcc — a CardCycle operation occurrence; `cycle` is the subject (pre/post are its
    CycleState records). */
abstract sig CycleOcc extends StatefulAction { cycle: one CardCycle }
fact CycleOccRecords { all o: CycleOcc | (o.pre + o.post) in CycleState }

sig RequestOcc            extends CycleOcc { qtyOverride: lone Quantity } { bindings = cycle + qtyOverride }
sig AcceptOcc             extends CycleOcc {} { bindings = cycle }
sig ShelveOcc             extends CycleOcc {} { bindings = cycle }
sig StartProcessingOcc    extends CycleOcc { pool: one EntityId } { bindings = cycle + pool }   // ATTACHES the pool (exclusive while the cycle lives)
sig CompleteProcessingOcc extends CycleOcc {} { bindings = cycle }
sig FulfillOcc            extends CycleOcc {} { bindings = cycle }
sig ReceiveOcc            extends CycleOcc {} { bindings = cycle }   // status-only: material arrivals are PoolAddOcc events on the attached pool
sig UseOcc                extends CycleOcc {} { bindings = cycle }
sig DepleteOcc            extends CycleOcc {} { bindings = cycle }
sig WithdrawOcc           extends CycleOcc {} { bindings = cycle }
sig ProductionFailureOcc  extends CycleOcc {} { bindings = cycle }   // IN_PROCESS → REQUESTING (2nd sanctioned backward, R8): the run closed with no inventory for this cycle; the pool DETACHES (back to the demand leg)

/** targetOf — the operation's CANONICAL target status (none for the closing Withdraw). */
fun targetOf[o: CycleOcc]: lone KanbanCardStatus {
  o in RequestOcc => REQUESTING else o in AcceptOcc => REQUESTED
  else o in ShelveOcc => REQUESTING else o in StartProcessingOcc => IN_PROCESS
  else o in CompleteProcessingOcc => READY else o in FulfillOcc => FULFILLING
  else o in ReceiveOcc => FULFILLED else o in UseOcc => IN_USE
  else o in DepleteOcc => DEPLETED
  else o in ProductionFailureOcc => REQUESTING else none
}

// (Materials are POOL-mediated since 2026-07-03 — KD12 revised: the record carries `sPool`, typed
// in cycle_state.als; tenancy + EXCLUSIVITY are the ATTACH guard below. A pool with residual stock
// may attach (over-receiving leftovers — Miguel); at rollover the pool is DISMISSED implicitly:
// the closed cycle's records are history and the new cycle is born pool-less — no operation
// needed; the pool atom persists and becomes attachable again. Explicit detachment for exception
// paths (unusable/excess materials) is DEFERRED. Receiving puts InventoryItems INTO the pool via
// its own log (PoolAddOcc), interleaved on the shared Tick order — the accrual-window coupling
// law is DT-014 rung 4.)

// ── refusal reasons ─────────────────────────────────────────────────────────────────────────────
one sig RClosed,            // the cycle is not live (never started, withdrawn, or rolled over)
        RBackward,          // target is not strictly forward on the region order
        RInactiveTarget,    // the deployment does not use the target status
        RSkippedActive,     // the jump skips a status the deployment DOES use
        RAlreadyStarted,    // genesis on a cycle that already has committed history
        RCardInCirculation, // genesis while the predecessor cycle is still open
        RNotRequested,      // Shelve from a status other than REQUESTED
        RPoolInUse,         // attach: another LIVE cycle currently holds this pool (exclusivity)
        RForeignPool,       // attach: the pool must be in the cycle's tenant
        RNotInProcess       // ProductionFailure from a status other than IN_PROCESS (R8)
        extends Reason {}

// ── chaining (unconditional — refusals read the real state) ─────────────────────────────────────
/** priorCycleOcc — the latest committed occurrence on the same cycle before `o`. */
fun priorCycleOcc[o: CycleOcc]: lone CycleOcc {
  { b: CycleOcc | committed[b] and b.cycle = o.cycle and precedes[b.tick, o.tick]
      and (no c: CycleOcc | committed[c] and c.cycle = o.cycle
             and precedes[b.tick, c.tick] and precedes[c.tick, o.tick]) }
}
fact CycleChaining {
  all o: CycleOcc | let pr = priorCycleOcc[o] | (some pr => o.pre = pr.post else no o.pre)
}

// ── closure (withdraw | rollover) and liveness, relative to a log position ─────────────────────
/** closedStrictlyBefore — the cycle was closed before `t`: withdrawn, or its successor's genesis
    committed (the rollover closes the predecessor). */
pred closedStrictlyBefore[c: CardCycle, t: Tick] {
  (some w: WithdrawOcc | committed[w] and w.cycle = c and precedes[w.tick, t])
  or (some r: RequestOcc | committed[r] and r.cycle.precededBy = c and precedes[r.tick, t])
}
/** liveAtOcc — the cycle is STARTED and OPEN when `o` executes (what its guards read). */
pred liveAtOcc[o: CycleOcc] { some o.pre and not closedStrictlyBefore[o.cycle, o.tick] }

// ── reason-precise admission guards (Accepted ⟺ ∅; because = EXACTLY the set) ───────────────────
/** requestViol — genesis: a fresh cycle, whose predecessor (if any) is closed, into an active
    REQUESTING. */
fun requestViol[o: RequestOcc]: set Reason {
  ((some b: CycleOcc | committed[b] and b.cycle = o.cycle and precedes[b.tick, o.tick])
     => RAlreadyStarted else none)
  + ((some o.cycle.precededBy and not closedStrictlyBefore[o.cycle.precededBy, o.tick])
     => RCardInCirculation else none)
  + ((REQUESTING not in LifecycleConfig.active) => RInactiveTarget else none)
}
/** forwardViol — the forward-skip discipline (KD9): strictly forward, into an active status,
    skipping only inactive ones. */
fun forwardViol[o: CycleOcc]: set Reason {
  ((not liveAtOcc[o]) => RClosed else none)
  + ((liveAtOcc[o] and not regionBefore[o.pre.sStatus, targetOf[o]]) => RBackward else none)
  + ((targetOf[o] not in LifecycleConfig.active) => RInactiveTarget else none)
  + ((liveAtOcc[o] and regionBefore[o.pre.sStatus, targetOf[o]]
      and some m: LifecycleConfig.active | regionBetween[m, o.pre.sStatus, targetOf[o]])
     => RSkippedActive else none)
}
/** startViol — StartProcessing = the forward step PLUS the pool attach: the resolved pool (if it
    resolves — dangling allowed, soft ref) must be in-tenant and not held by another LIVE cycle
    (EXCLUSIVE while the holder lives — Miguel 2026-07-03). Residue is ALLOWED: a pool with
    left-over stock (e.g. over-receiving) may attach directly — with enough stock the cycle can
    move straight on toward READY. */
fun startViol[o: StartProcessingOcc]: set Reason {
  forwardViol[o]
  + ((some p: resolve[o.pool] & InventoryPool | p.tenantId != o.cycle.tenantId) => RForeignPool else none)
  + ((some p: resolve[o.pool] & InventoryPool | some c2: CardCycle - o.cycle |
        liveCycleAt[c2, o.tick] and resolve[stateOfCycleAt[c2, o.tick].sPool] = p)
     => RPoolInUse else none)
}
/** shelveViol — the sanctioned backward operation: exactly REQUESTED → REQUESTING. */
fun shelveViol[o: ShelveOcc]: set Reason {
  ((not liveAtOcc[o]) => RClosed else none)
  + ((liveAtOcc[o] and o.pre.sStatus != REQUESTED) => RNotRequested else none)
  + ((REQUESTING not in LifecycleConfig.active) => RInactiveTarget else none)
}
/** withdrawViol — closing an open cycle. */
fun withdrawViol[o: WithdrawOcc]: set Reason { (not liveAtOcc[o]) => RClosed else none }
/** productionFailureViol — the SECOND sanctioned backward operation (R8, amended 2026-07-06):
    exactly IN_PROCESS → REQUESTING (the completing production run allocated this cycle nothing;
    it re-enters the waiting queue, attachable by a new DemandItem). */
fun productionFailureViol[o: ProductionFailureOcc]: set Reason {
  ((not liveAtOcc[o]) => RClosed else none)
  + ((liveAtOcc[o] and o.pre.sStatus != IN_PROCESS) => RNotInProcess else none)
  + ((REQUESTING not in LifecycleConfig.active) => RInactiveTarget else none)
}

fun cycleForwardOps: set CycleOcc {
  AcceptOcc + StartProcessingOcc + CompleteProcessingOcc + FulfillOcc + ReceiveOcc + UseOcc + DepleteOcc
}
fact CycleAdmissionWitness {
  all o: RequestOcc  | (o.admission = Accepted iff no requestViol[o])  and (o.admission in Rejected implies o.admission.because = requestViol[o])
  all o: cycleForwardOps - StartProcessingOcc | (o.admission = Accepted iff no forwardViol[o]) and (o.admission in Rejected implies o.admission.because = forwardViol[o])
  all o: StartProcessingOcc | (o.admission = Accepted iff no startViol[o]) and (o.admission in Rejected implies o.admission.because = startViol[o])
  all o: ShelveOcc   | (o.admission = Accepted iff no shelveViol[o])   and (o.admission in Rejected implies o.admission.because = shelveViol[o])
  all o: WithdrawOcc | (o.admission = Accepted iff no withdrawViol[o]) and (o.admission in Rejected implies o.admission.because = withdrawViol[o])
  all o: ProductionFailureOcc | (o.admission = Accepted iff no productionFailureViol[o]) and (o.admission in Rejected implies o.admission.because = productionFailureViol[o])
}
// No result policy in v1 (mirrors the InventoryItem and pool logs).
fact CycleCommitAccepts { all o: CycleOcc | some o.commit implies o.commit = Accepted }

// ── effects (committed) — per-kind frames on the record ────────────────────────────────────────
pred sameCyclePayloadButStatus[b, a: CycleState] {
  a.sLocator = b.sLocator and a.sPool = b.sPool and a.sQuantityOverride = b.sQuantityOverride
}
fact CycleEffectWitness {
  all o: RequestOcc | committed[o] implies {
    o.post.sStatus = REQUESTING
    no o.post.sPool                            // the demanding leg carries no bin (KD12 revised)
    o.post.sQuantityOverride = o.qtyOverride
    no (o.post & CycleState).sLocator          // dormant until the rung-4 writer (& CycleState: sLocator is ambiguous vs InventoryItemState since DT-017 brought the II record into the pool cone)
  }
  all o: cycleForwardOps - StartProcessingOcc | committed[o] implies {
    o.post.sStatus = targetOf[o] and sameCyclePayloadButStatus[o.pre, o.post]
  }
  all o: StartProcessingOcc | committed[o] implies {
    o.post.sStatus = IN_PROCESS
    o.post.sPool = o.pool                      // the pool ATTACHES (exclusive while live) and stays frozen
    (o.post & CycleState).sLocator = (o.pre & CycleState).sLocator and o.post.sQuantityOverride = o.pre.sQuantityOverride
  }
  all o: ShelveOcc | committed[o] implies {
    o.post.sStatus = REQUESTING and sameCyclePayloadButStatus[o.pre, o.post]
  }
  all o: WithdrawOcc | committed[o] implies o.post = o.pre      // the TOMBSTONE (closing; abandoned)
  all o: ProductionFailureOcc | committed[o] implies {          // back to the waiting queue (R8)
    o.post.sStatus = REQUESTING
    no o.post.sPool                            // the pool DETACHES — REQUESTED is the demand leg again
    (o.post & CycleState).sLocator = (o.pre & CycleState).sLocator
    o.post.sQuantityOverride = o.pre.sQuantityOverride
  }
}

// ── the projections (the notifications surface) ────────────────────────────────────────────────
/** lastCycleTouch — the latest committed occurrence on `c` at-or-before `t`. */
fun lastCycleTouch[c: CardCycle, t: Tick]: lone CycleOcc {
  { o: CycleOcc | committed[o] and o.cycle = c and notAfter[o.tick, t]
      and (no b: CycleOcc | committed[b] and b.cycle = c and notAfter[b.tick, t]
             and precedes[o.tick, b.tick]) }
}
/** stateOfCycleAt — LOCF of records: the cycle's payload as of `t`. */
fun stateOfCycleAt[c: CardCycle, t: Tick]: lone CycleState { lastCycleTouch[c, t].post }
/** statusAt — the cycle's operational status as of `t`. */
fun statusAt[c: CardCycle, t: Tick]: lone KanbanCardStatus { stateOfCycleAt[c, t].sStatus }
/** closedAt — the cycle is closed as of `t` (withdrawn or rolled over). */
pred closedAt[c: CardCycle, t: Tick] {
  (some w: WithdrawOcc | committed[w] and w.cycle = c and notAfter[w.tick, t])
  or (some r: RequestOcc | committed[r] and r.cycle.precededBy = c and notAfter[r.tick, t])
}
/** liveCycleAt — started and open as of `t` (the SQ-8 "live" reading). */
pred liveCycleAt[c: CardCycle, t: Tick] { some lastCycleTouch[c, t] and not closedAt[c, t] }
/** completedAt / abandonedAt — the SQ-8 "done" readings, DERIVED from how the cycle closed. */
pred completedAt[c: CardCycle, t: Tick] {
  some r: RequestOcc | committed[r] and r.cycle.precededBy = c and notAfter[r.tick, t]
}
pred abandonedAt[c: CardCycle, t: Tick] {
  some w: WithdrawOcc | committed[w] and w.cycle = c and notAfter[w.tick, t]
}
