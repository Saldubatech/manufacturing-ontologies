module operations/demand/demand_implementation

/*
 * DEMAND — IMPLEMENTATION (DT-016/DT-017). The log machinery: spine adoption, reason-precise
 * admission guards, and per-kind effects (record frames). The demand ↔ kanban interactions are
 * CONVERGENT/OPERATION with the CALL-FIRST saga shape (see demand_contracts.als): there is NO
 * cross-log enforcement fact — the demand guards ARE the saga commit gates, reading the member
 * cycles' current states; in-flight intermediates are legal. Integration roots open this file
 * to get the REAL module.
 *
 * GUARDS READ `o.pre` (the chained record — the state the operation actually saw; refusals
 * included). Cycle-side reads at `o.tick` are STRICTLY-BEFORE state: OneOccurrencePerTick means
 * `o` itself occupies the tick.
 *
 * ResetQty's Σ effect is CONFINED (R3b): demand_reset.als (opened ONLY by its dedicated root)
 * carries the arity-4 fold; HERE the effect frames everything except sDemandQty. Roots outside
 * the dedicated one must treat a committed ResetQty's quantity as UNSPECIFIED.
 */

open operations/demand/demand_contracts
open meta/subject_log/subject_log[DemandItem, DemandState] as dlog   // same params ⇒ the SAME spine instance as demand_types

// ── spine adoption (DT-015 Q5) ──────────────────────────────────────────────────────────────────
fact DemandChaining      { dlog/chained }
fact DemandCommitAccepts { dlog/commitAlwaysAccepts }   // v1 result policy (no commit-gate refusals)

// ── guard-side reads ────────────────────────────────────────────────────────────────────────────
/** liveAtOccD — the demand item is STARTED and LIVE as the operation reads it (pre-record). */
pred liveAtOccD[o: dlog/SubjectOcc] { some o.pre and dPre[o].sStatus in liveStatuses }
/** startedBeforeD — the subject has committed history strictly before `o`. */
pred startedBeforeD[o: dlog/SubjectOcc] {
  some b: dlog/SubjectOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
}
/** deletedBeforeD — a committed Delete tombstone exists strictly before `o`. */
pred deletedBeforeD[o: dlog/SubjectOcc] {
  some b: DeleteDemandOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
}
// (preMemberCycles / preLiveMemberRefs moved to demand_types — the contracts' commit-gate laws
// read them too.)

// ── reason-precise admission guards (Accepted ⟺ ∅; because = EXACTLY the set) ───────────────────
/** createGenesisViol — the genesis conditions shared by both create kinds. (NO uniqueness check —
    R1 amended: multiple DemandItems per (Item, Source Station) are legal; single-OPEN, if a
    deployment wants it, is CALLER policy over the `demandsFor` read.) */
fun createGenesisViol[o: dlog/SubjectOcc, item, station: EntityId]: set Reason {
  (startedBeforeD[o] => RDemandStarted else none)
  + ((some i: resolve[item] & Item | i.tenantId != o.subject.tenantId) => RForeignRef else none)
  + ((some s: resolve[station] & Station | s.tenantId != o.subject.tenantId) => RForeignRef else none)
}
/** attachCycleViol — the SAGA COMMIT GATE for attach (C/OP call-first): the member must be an
    in-tenant, live cycle standing at REQUESTED (its Accept — the saga's first leg — already
    committed) and held by no live demand. Conservative refusal on a dangling ref. NB the held
    check excludes `o.subject`: a demand read at `o.tick` would see o's OWN commit (LOCF reads
    are inclusive) and refuse itself; OTHER demands' reads at `o.tick` are strictly-before by
    OneOccurrencePerTick. Already-a-member-of-THIS-demand is the separate pre-side check. */
fun attachCycleViol[o: dlog/SubjectOcc, m: EntityId]: set Reason {
  (let c = resolve[m] & CardCycle |
    ((some c and c.tenantId != o.subject.tenantId) => RForeignCycle else none)
    + ((no c or not liveCycleAt[c, o.tick] or statusAt[c, o.tick] != REQUESTED)
       => RCycleIneligible else none)
    + ((some c and some d2: DemandItem - o.subject | liveDemandAt[d2, o.tick] and c in attachedAt[d2, o.tick])
       => RCycleHeld else none)
    + ((m in dPre[o].sMembership) => RCycleHeld else none))
}
fun createViol[o: CreateDemandOcc]: set Reason { createGenesisViol[o, o.item, o.station] }
fun createWithViol[o: CreateWithCycleOcc]: set Reason {
  createGenesisViol[o, o.item, o.station] + attachCycleViol[o, o.member]
}
fun addViol[o: AddCycleOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_OPEN) => RFrozen else none)
  + attachCycleViol[o, o.member]
}
fun removeViol[o: RemoveCycleOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_OPEN) => RFrozen else none)
  + ((o.member not in dPre[o].sMembership) => RNotAttached else none)
  + ((let c = resolve[o.member] & CardCycle |
       no c or not liveCycleAt[c, o.tick] or statusAt[c, o.tick] != REQUESTING)
     => RCycleIneligible else none)   // C/OP gate: the member's Shelve (saga's first leg) already committed
}
fun detachWithdrawnViol[o: DetachWithdrawnOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_OPEN) => RFrozen else none)
  + ((o.member not in dPre[o].sMembership) => RNotAttached else none)
  + ((some c: resolve[o.member] & CardCycle | liveCycleAt[c, o.tick]) => RCycleLive else none)
}
fun adjustViol[o: AdjustQtyOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_OPEN) => RFrozen else none)
}
fun resetViol[o: ResetQtyOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_OPEN) => RFrozen else none)
}
fun releaseViol[o: ReleaseOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_OPEN) => RBadState else none)
}
fun reopenViol[o: ReopenOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_RELEASED) => RBadState else none)
}
fun startProductionViol[o: StartProductionOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_RELEASED) => RBadState else none)
  + ((some p: resolve[o.holding] & InventoryPool | p.tenantId != o.subject.tenantId)
     => RForeignRef else none)
  + ((liveAtOccD[o] and dPre[o].sStatus = DS_RELEASED
      and some c: preMemberCycles[o] | statusAt[c, o.tick] != IN_PROCESS)
     => RCycleIneligible else none)   // C/OP gate: every live member's StartProcessing (saga's first legs) already committed
}
fun recordProductionViol[o: RecordProductionOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_IN_PROCESS) => RBadState else none)
  + ((some p: resolve[o.delivery] & InventoryPool | p.tenantId != o.subject.tenantId)
     => RForeignRef else none)
}
fun distributeViol[o: DistributeOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_IN_PROCESS) => RBadState else none)
  + ((liveAtOccD[o] and (o.allocation.Quantity + o.fills) not in preLiveMemberRefs[o])
     => RBadAllocation else none)     // retired members receive NOTHING (R7/R8)
  + ((liveAtOccD[o] and some m: o.fills | some c: resolve[m] & CardCycle | statusAt[c, o.tick] != READY)
     => RCycleIneligible else none)   // C/OP gate: each fill's CompleteProcessing (saga's first leg) already committed
}
fun completeViol[o: CompleteOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_IN_PROCESS) => RBadState else none)
  + ((liveAtOccD[o] and some heldAt[resolve[dPre[o].sHolding] & InventoryPool, o.tick])
     => RUndistributed else none)
  + ((liveAtOccD[o] and some c: preMemberCycles[o] | statusAt[c, o.tick] = IN_PROCESS)
     => RCycleIneligible else none)   // C/OP gate: every member SETTLED first (READY or back to REQUESTING)
}
fun cancelViol[o: CancelOcc]: set Reason {
  ((not liveAtOccD[o]) => RDemandClosed else none)
  + ((liveAtOccD[o] and dPre[o].sStatus != DS_OPEN) => RBadState else none)
  + ((liveAtOccD[o] and dPre[o].sStatus = DS_OPEN and some dPre[o].sMembership) => RHasCards else none)
}
fun deleteViol[o: DeleteDemandOcc]: set Reason {
  ((not startedBeforeD[o] or deletedBeforeD[o]) => RDemandClosed else none)
  + ((startedBeforeD[o] and dPre[o].sStatus in liveStatuses) => RNotTerminal else none)
}

fact DemandAdmissionWitness {
  all o: CreateDemandOcc     | (o.admission = Accepted iff no createViol[o])           and (o.admission in Rejected implies o.admission.because = createViol[o])
  all o: CreateWithCycleOcc  | (o.admission = Accepted iff no createWithViol[o])       and (o.admission in Rejected implies o.admission.because = createWithViol[o])
  all o: AddCycleOcc         | (o.admission = Accepted iff no addViol[o])              and (o.admission in Rejected implies o.admission.because = addViol[o])
  all o: RemoveCycleOcc      | (o.admission = Accepted iff no removeViol[o])           and (o.admission in Rejected implies o.admission.because = removeViol[o])
  all o: DetachWithdrawnOcc  | (o.admission = Accepted iff no detachWithdrawnViol[o])  and (o.admission in Rejected implies o.admission.because = detachWithdrawnViol[o])
  all o: AdjustQtyOcc        | (o.admission = Accepted iff no adjustViol[o])           and (o.admission in Rejected implies o.admission.because = adjustViol[o])
  all o: ResetQtyOcc         | (o.admission = Accepted iff no resetViol[o])            and (o.admission in Rejected implies o.admission.because = resetViol[o])
  all o: ReleaseOcc          | (o.admission = Accepted iff no releaseViol[o])          and (o.admission in Rejected implies o.admission.because = releaseViol[o])
  all o: ReopenOcc           | (o.admission = Accepted iff no reopenViol[o])           and (o.admission in Rejected implies o.admission.because = reopenViol[o])
  all o: StartProductionOcc  | (o.admission = Accepted iff no startProductionViol[o])  and (o.admission in Rejected implies o.admission.because = startProductionViol[o])
  all o: RecordProductionOcc | (o.admission = Accepted iff no recordProductionViol[o]) and (o.admission in Rejected implies o.admission.because = recordProductionViol[o])
  all o: DistributeOcc       | (o.admission = Accepted iff no distributeViol[o])       and (o.admission in Rejected implies o.admission.because = distributeViol[o])
  all o: CompleteOcc         | (o.admission = Accepted iff no completeViol[o])         and (o.admission in Rejected implies o.admission.because = completeViol[o])
  all o: CancelOcc           | (o.admission = Accepted iff no cancelViol[o])           and (o.admission in Rejected implies o.admission.because = cancelViol[o])
  all o: DeleteDemandOcc     | (o.admission = Accepted iff no deleteViol[o])           and (o.admission in Rejected implies o.admission.because = deleteViol[o])
}

// ── effects (committed) — per-kind frames on the record ────────────────────────────────────────
/** sameDemandButStatus — everything except the status is carried over. */
pred sameDemandButStatus[b, a: DemandState] {
  a.sDemandQty = b.sDemandQty and a.sMembership = b.sMembership
  and a.sItem = b.sItem and a.sStation = b.sStation and a.sHolding = b.sHolding
}
/** sameKeyAndHolding — the immutable collation key and the holding ref are carried over. */
pred sameKeyAndHolding[b, a: DemandState] {
  a.sItem = b.sItem and a.sStation = b.sStation and a.sHolding = b.sHolding
}

fact DemandEffectWitness {
  all o: CreateDemandOcc | committed[o] implies {
    dPost[o].sStatus = DS_OPEN
    dPost[o].sDemandQty = o.qty                       // seeds the advisory intent (R3b)
    no dPost[o].sMembership
    dPost[o].sItem = o.item and dPost[o].sStation = o.station
    no dPost[o].sHolding
  }
  all o: CreateWithCycleOcc | committed[o] implies {
    dPost[o].sStatus = DS_OPEN
    qtyMap[dPost[o].sDemandQty] = add[qtyMap[o.qty], effectiveQtyMap[resolve[o.member] & CardCycle]]
    dPost[o].sMembership = o.member
    dPost[o].sItem = o.item and dPost[o].sStation = o.station
    no dPost[o].sHolding
  }
  all o: AddCycleOcc | committed[o] implies {
    dPost[o].sStatus = dPre[o].sStatus
    qtyMap[dPost[o].sDemandQty] = add[qtyMap[dPre[o].sDemandQty], effectiveQtyMap[resolve[o.member] & CardCycle]]
    dPost[o].sMembership = dPre[o].sMembership + o.member
    sameKeyAndHolding[dPre[o], dPost[o]]
  }
  all o: RemoveCycleOcc + DetachWithdrawnOcc | committed[o] implies {
    dPost[o].sStatus = dPre[o].sStatus
    qtyMap[dPost[o].sDemandQty] = add[qtyMap[dPre[o].sDemandQty], negate[effectiveQtyMap[resolve[o.member] & CardCycle]]]
    dPost[o].sMembership = dPre[o].sMembership - o.member
    sameKeyAndHolding[dPre[o], dPost[o]]
  }
  all o: AdjustQtyOcc | committed[o] implies {
    dPost[o].sStatus = dPre[o].sStatus
    dPost[o].sDemandQty = o.qty                       // SET (R3b; delta-adjust is client sugar)
    dPost[o].sMembership = dPre[o].sMembership
    sameKeyAndHolding[dPre[o], dPost[o]]
  }
  all o: ResetQtyOcc | committed[o] implies {       // Σ semantics CONFINED to demand_reset.als
    dPost[o].sStatus = dPre[o].sStatus
    dPost[o].sMembership = dPre[o].sMembership
    sameKeyAndHolding[dPre[o], dPost[o]]
  }
  all o: ReleaseOcc | committed[o] implies
    { dPost[o].sStatus = DS_RELEASED and sameDemandButStatus[dPre[o], dPost[o]] }
  all o: ReopenOcc | committed[o] implies
    { dPost[o].sStatus = DS_OPEN and sameDemandButStatus[dPre[o], dPost[o]] }
  all o: StartProductionOcc | committed[o] implies {
    dPost[o].sStatus = DS_IN_PROCESS
    dPost[o].sHolding = o.holding                     // the accumulation pool attaches (R8)
    dPost[o].sDemandQty = dPre[o].sDemandQty
    dPost[o].sMembership = dPre[o].sMembership
    dPost[o].sItem = dPre[o].sItem and dPost[o].sStation = dPre[o].sStation
  }
  all o: RecordProductionOcc | committed[o] implies o.post = o.pre   // ⟲ — the delivery lands on the POOL log
  all o: DistributeOcc       | committed[o] implies o.post = o.pre   // ⟲ — allocation moves pools + cycles, not this record
  all o: CompleteOcc | committed[o] implies
    { dPost[o].sStatus = DS_COMPLETE and sameDemandButStatus[dPre[o], dPost[o]] }
  all o: CancelOcc | committed[o] implies
    { dPost[o].sStatus = DS_CANCELED and sameDemandButStatus[dPre[o], dPost[o]] }
  all o: DeleteDemandOcc | committed[o] implies o.post = o.pre       // the tombstone (II precedent, R7)
}

// (NO cross-log enforcement facts — C/OP, 2026-07-06: the guards above ARE the saga commit
// gates; the commit-gate contract laws are THEOREMS of them, and the quiescence law
// `demandCyclesAlignedAt` is witnessed on settled traces, never asserted globally.)
