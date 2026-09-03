module soak/sliced/intent_log_arche_inductive

/*
 * E7 generalization ladder — the INTENT LOG's CITATION laws (DT-029 E1/E2 rung, SAMWISE; HOLD arm): the
 * inductiveness check of the three PREMISE-FREE laws the pattern guarantees once every occurrence carries its
 * origin (`arche`, meta/occurrence) and the owner reads moved-by-this from citations (`claim/citationView`, adopted):
 *   A — ATTRIBUTION SOUNDNESS: a committed view reads moved-by-this iff a committed peer row ON THE SUBJECT cites
 *       the intent it settles (the module's `citers` are not subject-restricted; this slice's guards make them so);
 *   B — LATE-ACT NON-CONFIRMABILITY: every committed peer row credited by a committed CONFIRM landed while the
 *       chain was LIVE — a row citing an intent that was already free at its tick never yields a CONFIRM;
 *   C — CONFIRMED-INTENT SOUNDNESS: a committed CONFIRM has EXACTLY ONE committed peer row on its subject citing
 *       the intent it settles (uniqueness per (arche, subject) + the citation).
 * Successor of intent_log_claim_inductive (D3, the exclusive-arm rung under `takeOnlyByClaimants`): the same slot
 * slice, the premise REMOVED, takes carry `arche`. THE SLICE'S OWN CHOICES, flagged for review (DT-029 §3.3): the
 * peer REFUSES a take citing anything but the committed OPENER of this slot's chain (`RForeignClaim` — the
 * callee-side validation of the citation's target; a foreign or stale citation is representable AND refused) and a
 * park citing anything but the pending ACT opener; a re-sent origin is refused `RDuplicateArche`; havoc seeds cite
 * nothing and ARE the citable opener when they open a live phase. Uncited takes (the UI case) are admitted and
 * read moved-OTHERWISE. Base-scope obligations by day; `_w` / `_s` gates in a NIGHTWATCH window.
 */

open meta/kernel
open meta/action/stateful
open meta/intent_log/semantics as sem
open meta/intent_log/intent_log[Slot, sem/HoldSem] as claim
open meta/subject_log/subject_log[Slot, SlotRec] as slog
open meta/model_time/model_time as mt
open util/ordering[mt/Tick] as tord

// ── the peer: a Slot with its own log (no holder knowledge; validates the citation's target) ──────
abstract sig SlotStatus {}
one sig S_FREE, S_TAKEN, S_RETIRED extends SlotStatus {}
sig Slot extends Scoped {}
fact SlotRefs { all s: Slot | no s.dataRefs }
sig SlotRec extends Snapshot { sStat: one SlotStatus }
fact SlotRecExtensional { all disj a, b: SlotRec | a.sStat != b.sStat }

sig AddSlotOcc extends slog/SubjectOcc {} { bindings = subject }   // genesis → FREE
sig TakeOcc    extends slog/SubjectOcc {} { bindings = subject }   // FREE → TAKEN; cites the claim's opener, or nothing (the UI)
sig ParkOcc    extends slog/SubjectOcc {} { bindings = subject }   // TAKEN → FREE; cites the pending ACT opener, or nothing
sig RetireOcc  extends slog/SubjectOcc {} { bindings = subject }   // → RETIRED

fun sPre [o: slog/SubjectOcc]: lone SlotRec { o.pre  & SlotRec }
fun sPost[o: slog/SubjectOcc]: lone SlotRec { o.post & SlotRec }
fun slotStatusAt[s: Slot, t: Tick]: lone SlotStatus { slog/recordAt[s, t].sStat }

one sig RSlotStarted, RSlotUnborn, RSlotBusy, RSlotFree, RSlotGone, RForeignClaim extends Reason {}
/** foreignTake / foreignPark — a citation whose target is not this slot's committed opener / pending act opener. */
pred foreignTake[o: TakeOcc] { o.arche != o and o.arche != claim/openerBefore[o.subject, o.tick] }
pred foreignPark[o: ParkOcc] { o.arche != o and o.arche != claim/actOpenerBefore[o.subject, o.tick] }
fun addSlotViol[o: AddSlotOcc]: set Reason { (some slog/priorOn[o]) => RSlotStarted else none }
fun takeViol[o: TakeOcc]: set Reason {
  ((no o.pre) => RSlotUnborn else none)
  + ((sPre[o].sStat = S_TAKEN) => RSlotBusy else none)
  + ((sPre[o].sStat = S_RETIRED) => RSlotGone else none)
  + (foreignTake[o] => RForeignClaim else none)
  + (slog/archeDuplicate[o] => sem/RDuplicateArche else none)
}
fun parkViol[o: ParkOcc]: set Reason {
  ((no o.pre) => RSlotUnborn else none)
  + ((sPre[o].sStat = S_FREE) => RSlotFree else none)
  + ((sPre[o].sStat = S_RETIRED) => RSlotGone else none)
  + (foreignPark[o] => RForeignClaim else none)
  + (slog/archeDuplicate[o] => sem/RDuplicateArche else none)
}
fun retireViol[o: RetireOcc]: set Reason {
  ((no o.pre) => RSlotUnborn else none) + ((sPre[o].sStat = S_RETIRED) => RSlotGone else none)
}
fact SlotAdmission {
  all o: AddSlotOcc | (o.admission = Accepted iff no addSlotViol[o]) and (o.admission in Rejected implies o.admission.because = addSlotViol[o])
  all o: TakeOcc    | (o.admission = Accepted iff no takeViol[o])    and (o.admission in Rejected implies o.admission.because = takeViol[o])
  all o: ParkOcc    | (o.admission = Accepted iff no parkViol[o])    and (o.admission in Rejected implies o.admission.because = parkViol[o])
  all o: RetireOcc  | (o.admission = Accepted iff no retireViol[o])  and (o.admission in Rejected implies o.admission.because = retireViol[o])
}
fact SlotEffects {
  all o: AddSlotOcc | committed[o] implies sPost[o].sStat = S_FREE
  all o: TakeOcc    | committed[o] implies sPost[o].sStat = S_TAKEN
  all o: ParkOcc    | committed[o] implies sPost[o].sStat = S_FREE
  all o: RetireOcc  | committed[o] implies sPost[o].sStat = S_RETIRED
}
fact SlotSpine { slog/chained and slog/commitAlwaysAccepts and slog/archeUniquePerSubject }
fact SlotOriginsCite { all o: AddSlotOcc + RetireOcc | o.arche = o }   // genesis and retirement are nobody's leg

// ── the owner side: the claim chain over Slot, bindings, the adopted citation view + the residual ─
sig Owner extends Scoped {}
fact OwnerRefs { all o: Owner | no o.dataRefs }
sig Version {}
one sig ParkAct {}
fact ClaimSpine { claim/spineAdopted }
fact ClaimAttribution { claim/citationView }   // DT-029 E2: moved-by-this = a committed row outside this log cites the intent
fact ClaimBindings {
  all o: claim/HolderOcc   | o.holder in Owner.eId
  all o: claim/TransferOcc | o.from in Owner.eId and o.to in Owner.eId and o.toVersion in Version
  all o: claim/ReserveOcc  | o.ownerVersion in Version
  all o: claim/CitingOcc   | o.peerRid in slog/SubjectOcc
  all o: claim/ActReserveOcc | o.act = ParkAct and o.mode = sem/AM_CLOSE
  all r: claim/IntentRec   | r.iVersion in Version and (some r.iAct implies r.iAct = ParkAct)
  all o: claim/IntentOcc   | o.arche = o   // the owner's rows are originators here (no saga above them, E3)
}
/** The RESIDUAL split (D-2): when no committed row cites the intent — ABSENT before genesis, UNMOVED while the
    slot is in the act's precondition state, MOVED_OTHERWISE otherwise (taken by a stranger, retired). */
fun slotResidualAt[s: Slot, t: Tick]: one sem/PeerView {
  (no slog/recordAt[s, t])            => sem/PV_ABSENT
  else (slotStatusAt[s, t] = S_FREE)   => sem/PV_UNMOVED
  else sem/PV_MOVED_OTHERWISE
}
fun parkResidualAt[s: Slot, t: Tick]: one sem/PeerView {
  (no slog/recordAt[s, t])            => sem/PV_ABSENT
  else (slotStatusAt[s, t] = S_TAKEN)  => sem/PV_UNMOVED
  else sem/PV_MOVED_OTHERWISE
}
fact ClaimViews {
  all o: claim/ConfirmOcc + claim/ReleaseOcc       | not claim/cited[o] implies o.peerView = slotResidualAt[o.subject, o.tick]
  all o: claim/ActConfirmOcc + claim/ActReleaseOcc | not claim/cited[o] implies o.peerView = parkResidualAt[o.subject, o.tick]
}

// ── the three laws (premise-free) ──────────────────────────────────────────────────────────────
/** openerAt — the opener of the intent the slot is under at-or-before `t` (the rung's tick-level reading). */
fun openerAt[s: Slot, t: Tick]: lone claim/IntentOcc {
  { r: claim/IntentOcc | committed[r] and r.subject = s and notAfter[r.tick, t]
      and claim/prePhase[r] in sem/freePhases and claim/iPost[r].iPhase in sem/livePhases
      and no r2: claim/IntentOcc | committed[r2] and r2.subject = s and precedes[r.tick, r2.tick] and notAfter[r2.tick, t]
                                    and claim/prePhase[r2] in sem/freePhases and claim/iPost[r2].iPhase in sem/livePhases }
}
/** takesCiting — the committed takes on `s` citing intent `i`. */
fun takesCiting[s: Slot, i: claim/IntentOcc]: set TakeOcc { { x: TakeOcc | committed[x] and x.subject = s and x.arche = i } }
/** takesCitingAt — the same, at-or-before `t` (the invariant must never count a FUTURE take: the first base run's CTI). */
fun takesCitingAt[s: Slot, i: claim/IntentOcc, t: Tick]: set TakeOcc { { x: takesCiting[s, i] | notAfter[x.tick, t] } }
pred lawA {
  all o: claim/ViewOcc | committed[o] implies
    ((o.peerView = sem/PV_MOVED_BY_THIS) iff
     (some x: TakeOcc + ParkOcc | committed[x] and x.subject = o.subject and x.arche = claim/settledIntent[o] and precedes[x.tick, o.tick]))
}
pred lawB {
  all o: claim/ConfirmOcc + claim/ActConfirmOcc | committed[o] implies
    (all x: TakeOcc + ParkOcc | (committed[x] and x.subject = o.subject and x.arche = claim/settledIntent[o] and precedes[x.tick, o.tick])
       implies claim/phaseAt[o.subject, x.tick] in sem/livePhases)
}
pred lawC {
  all o: claim/ConfirmOcc | committed[o] implies one takesCiting[o.subject, claim/settledIntent[o]]
}

// ── the havoc seeds (one kind per log; seeds cite nothing and are citable openers when they open) ─
sig HavocSlotOcc  extends slog/SubjectOcc {} { bindings = subject }
sig HavocClaimOcc extends claim/IntentOcc {}  { bindings = subject }
fact HavocDiscipline {
  all h: HavocSlotOcc + HavocClaimOcc | h.admission = Accepted and h.arche = h
  all h: HavocSlotOcc,  o: slog/SubjectOcc - HavocSlotOcc   | precedes[h.tick, o.tick]
  all h: HavocClaimOcc, o: claim/IntentOcc - HavocClaimOcc  | precedes[h.tick, o.tick]
}
pred seedAt[t: Tick] { some h: HavocSlotOcc + HavocClaimOcc | h.tick = t }

// ── the candidate inductive invariant (per-tick slice) ─────────────────────────────────────────
/** While a slot's chain is live, the takes citing its opener are at most one, each landed while the chain was
    RESERVED; once held (HELD / ACTING) exactly one. */
pred e7Inv[t: Tick] {
  all s: Slot | let i = openerAt[s, t] | {
    claim/phaseAt[s, t] in sem/livePhases implies
      (lone takesCitingAt[s, i, t] and all x: takesCitingAt[s, i, t] | claim/phaseAt[s, x.tick] = sem/I_RESERVED)
    claim/phaseAt[s, t] in sem/heldPhases implies one takesCitingAt[s, i, t]
  }
}
/** The laws' per-tick slice: C — held ⇒ one citing take; B — every citing take landed while live. */
pred lawSliceAt[t: Tick] {
  all s: Slot | let i = openerAt[s, t] | {
    claim/phaseAt[s, t] in sem/heldPhases implies one takesCitingAt[s, i, t]
    all x: takesCitingAt[s, i, t] | claim/phaseAt[s, x.tick] in sem/livePhases
  }
}

// ── obligations ────────────────────────────────────────────────────────────────────────────────
assert e7_slice_faithful { (all t: Tick | lawSliceAt[t]) implies (lawB and lawC) }
assert e7_base { not seedAt[tord/first] implies e7Inv[tord/first] }
assert e7_step {
  all t: Tick - tord/last | let t2 = tord/next[t] | (e7Inv[t] and not seedAt[t2]) implies e7Inv[t2]
}
assert e7_law_A { lawA }
assert e7_law_B { (all t: Tick | e7Inv[t]) implies lawB }
assert e7_law_C { (all t: Tick | e7Inv[t]) implies lawC }

// ── vacuity guards (§3.3: all three take shapes, a confirmed chain; the two-subject witness is the sibling's) ──
run e7_seeded_citedTake {
  some hc: HavocClaimOcc, hs: HavocSlotOcc, k: TakeOcc |
    committed[hc] and claim/iPost[hc].iPhase = sem/I_RESERVED and committed[hs] and sPost[hs].sStat = S_FREE
    and committed[k] and k.subject = hc.subject and k.subject = hs.subject and k.arche = hc
    and precedes[hc.tick, k.tick] and precedes[hs.tick, k.tick]
} for 5 but 5 Int, 2 Slot, 2 Owner, 2 Version, 6 Tick, 5 Occurrence, 8 Snapshot, 8 EntityId expect 1
run e7_seeded_uncitedTake {
  some hc: HavocClaimOcc, hs: HavocSlotOcc, k: TakeOcc |
    committed[hc] and claim/iPost[hc].iPhase = sem/I_RESERVED and committed[hs] and sPost[hs].sStat = S_FREE
    and committed[k] and k.subject = hc.subject and k.subject = hs.subject and k.arche = k
    and precedes[hc.tick, k.tick] and precedes[hs.tick, k.tick]
} for 5 but 5 Int, 2 Slot, 2 Owner, 2 Version, 6 Tick, 5 Occurrence, 8 Snapshot, 8 EntityId expect 1
run e7_seeded_foreignCite {
  some disj s1, s2: Slot, hc: HavocClaimOcc, hs: HavocSlotOcc, k: TakeOcc |
    committed[hc] and hc.subject = s1 and claim/iPost[hc].iPhase = sem/I_RESERVED
    and committed[hs] and hs.subject = s2 and sPost[hs].sStat = S_FREE
    and k.subject = s2 and k.arche = hc and precedes[hc.tick, k.tick] and precedes[hs.tick, k.tick]
    and refusedAtAdmission[k] and k.admission.because = RForeignClaim
} for 5 but 5 Int, 2 Slot, 2 Owner, 2 Version, 6 Tick, 5 Occurrence, 8 Snapshot, 8 EntityId expect 1
run e7_seeded_confirmedChain {
  some hc: HavocClaimOcc, hs: HavocSlotOcc, k: TakeOcc, f: claim/ConfirmOcc |
    committed[hc] and claim/iPost[hc].iPhase = sem/I_RESERVED and committed[hs] and sPost[hs].sStat = S_FREE
    and committed[k] and committed[f] and k.subject = hc.subject and k.subject = hs.subject and f.subject = hc.subject
    and k.arche = hc and precedes[hc.tick, k.tick] and precedes[hs.tick, k.tick] and precedes[k.tick, f.tick]
    and claim/phaseAt[f.subject, f.tick] = sem/I_HELD
} for 5 but 5 Int, 2 Slot, 2 Owner, 2 Version, 6 Tick, 5 Occurrence, 8 Snapshot, 8 EntityId expect 1
// (`e7_seeded_transferTwoSubjectsOneArche` — one arche on two subjects — lives in the MOVEMENT-arm sibling
//  intent_log_arche_movement_inductive: under HOLD a take citing another slot's opener is FOREIGN and refused,
//  which the foreign-cite witness above pins; the legitimate two-subject case is a transfer's paired pours.)

check e7_slice_faithful for 5 but 5 Int, 2 Slot, 2 Owner, 2 Version, 6 Tick, 6 Occurrence, 8 Snapshot, 8 EntityId expect 0
check e7_base           for 5 but 5 Int, 2 Slot, 2 Owner, 2 Version, 6 Tick, 6 Occurrence, 8 Snapshot, 8 EntityId expect 0
check e7_step           for 5 but 5 Int, 2 Slot, 2 Owner, 2 Version, 6 Tick, 6 Occurrence, 8 Snapshot, 8 EntityId expect 0
check e7_law_A          for 5 but 5 Int, 2 Slot, 2 Owner, 2 Version, 6 Tick, 6 Occurrence, 8 Snapshot, 8 EntityId expect 0
check e7_law_B          for 5 but 5 Int, 2 Slot, 2 Owner, 2 Version, 6 Tick, 6 Occurrence, 8 Snapshot, 8 EntityId expect 0
check e7_law_C          for 5 but 5 Int, 2 Slot, 2 Owner, 2 Version, 6 Tick, 6 Occurrence, 8 Snapshot, 8 EntityId expect 0

// ── W-scope escalation (census-widened) and supersession gate (trace-collapsed) — window only ──
e7_step_w:  check e7_step  for 5 but 5 Int, 2 Slot, 2 Owner, 2 Version, 8 Tick, 8 Occurrence, 10 Snapshot, 8 EntityId expect 0
e7_law_w:   check e7_law_C for 5 but 5 Int, 2 Slot, 2 Owner, 2 Version, 8 Tick, 8 Occurrence, 10 Snapshot, 8 EntityId expect 0
e7_step_s:  check e7_step  for 6 but 5 Int, 3 Slot, 3 Owner, 3 Version, 6 Tick, 6 Occurrence, 9 Snapshot, 10 EntityId expect 0
e7_law_s:   check e7_law_C for 6 but 5 Int, 3 Slot, 3 Owner, 3 Version, 6 Tick, 6 Occurrence, 9 Snapshot, 10 EntityId expect 0
