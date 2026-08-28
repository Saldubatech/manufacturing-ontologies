module soak/sliced/intent_log_claim_inductive

/*
 * E7 generalization ladder — the INTENT LOG's cross-log law (DT-027 D3, SAMWISE): inductiveness
 * check of "a taken peer is always claimed" — the exemplar's `takenCartsAreClaimed` — on the
 * conventions/inductive_invariant idiom (order_frozen_outside_draft_inductive is the sibling for
 * the per-occurrence shape; read that header first).
 *
 * THE LAW (TWO LOGS): under the exclusive-arm PREMISE `takeOnlyByClaimants` (every committed
 * `take` on a slot saw a live RESERVE on the slot's claim chain — the runtime's "`accept` is
 * demand-only"), at every tick a TAKEN slot has a holder on its claim chain (`claim/holderAt`).
 * The peer (the slot log) keeps no holder knowledge; the law is discharged from the intent
 * chain's guards + effects (LC-IL-02/04/05/08) and the slot guards, state-locally.
 *
 * SELF-CONTAINED SLICE: a soak root may not open a conventions/ exemplar (layering lint), so the
 * slot log below is the exemplar's cart log in miniature (FREE / TAKEN / RETIRED; take, park,
 * retire; park is the CLOSE-mode act under the hold). SEEDS ON BOTH LOGS: HavocSlotOcc makes the
 * slot's state arbitrary; HavocClaimOcc makes the claim head arbitrary (any phase / holder / act);
 * both frame-free, always committed, strictly before every real occurrence; e7_step excludes steps
 * INTO a seed tick on either log.
 *
 * Base-scope obligations by day; `_w` / `_s` gates in a NIGHTWATCH window (declared).
 */

open meta/kernel
open meta/action/stateful
open meta/intent_log/semantics as sem
open meta/intent_log/intent_log[Slot, sem/HoldSem] as claim
open meta/subject_log/subject_log[Slot, SlotRec] as slog
open meta/model_time/model_time as mt
open util/ordering[mt/Tick] as tord

// ── the peer: a Slot with its own log (no holder knowledge) ────────────────────────────────────
abstract sig SlotStatus {}
one sig S_FREE, S_TAKEN, S_RETIRED extends SlotStatus {}
sig Slot extends Scoped {}
fact SlotRefs { all s: Slot | no s.dataRefs }
sig SlotRec extends Snapshot { sStat: one SlotStatus }
fact SlotRecExtensional { all disj a, b: SlotRec | a.sStat != b.sStat }

sig AddSlotOcc extends slog/SubjectOcc {} { bindings = subject }   // genesis → FREE
sig TakeOcc    extends slog/SubjectOcc {} { bindings = subject }   // FREE → TAKEN (the exclusive act)
sig ParkOcc    extends slog/SubjectOcc {} { bindings = subject }   // TAKEN → FREE (the CLOSE act under the hold)
sig RetireOcc  extends slog/SubjectOcc {} { bindings = subject }   // → RETIRED

fun sPre [o: slog/SubjectOcc]: lone SlotRec { o.pre  & SlotRec }
fun sPost[o: slog/SubjectOcc]: lone SlotRec { o.post & SlotRec }
fun slotStatusAt[s: Slot, t: Tick]: lone SlotStatus { slog/recordAt[s, t].sStat }

one sig RSlotStarted, RSlotUnborn, RSlotBusy, RSlotFree, RSlotGone extends Reason {}
fun addSlotViol[o: AddSlotOcc]: set Reason { (some slog/priorOn[o]) => RSlotStarted else none }
fun takeViol[o: TakeOcc]: set Reason {
  ((no o.pre) => RSlotUnborn else none)
  + ((sPre[o].sStat = S_TAKEN) => RSlotBusy else none)
  + ((sPre[o].sStat = S_RETIRED) => RSlotGone else none)
}
fun parkViol[o: ParkOcc]: set Reason {
  ((no o.pre) => RSlotUnborn else none)
  + ((sPre[o].sStat = S_FREE) => RSlotFree else none)
  + ((sPre[o].sStat = S_RETIRED) => RSlotGone else none)
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
fact SlotSpine { slog/chained and slog/commitAlwaysAccepts }

// ── the owner side: the claim chain over Slot, its bindings, the attribution facts ─────────────
sig Owner extends Scoped {}
fact OwnerRefs { all o: Owner | no o.dataRefs }
sig Version {}
/** ParkAct — the marker atom the park sub-intent names as its act. */
one sig ParkAct {}
fact ClaimSpine { claim/spineAdopted }
fact ClaimBindings {
  all o: claim/HolderOcc   | o.holder in Owner.eId
  all o: claim/TransferOcc | o.from in Owner.eId and o.to in Owner.eId and o.toVersion in Version
  all o: claim/ReserveOcc  | o.ownerVersion in Version
  all o: claim/CitingOcc   | o.peerRid in slog/SubjectOcc
  all o: claim/ActReserveOcc | o.act = ParkAct and o.mode = sem/AM_CLOSE   // the one act under the hold: park CLOSEs
  all r: claim/IntentRec   | r.iVersion in Version and (some r.iAct implies r.iAct = ParkAct)
}
/** The hold-level view of a slot relative to its claim. */
fun slotViewAt[s: Slot, t: Tick]: one sem/PeerView {
  (no slog/recordAt[s, t])            => sem/PV_ABSENT
  else (slotStatusAt[s, t] = S_FREE)   => sem/PV_UNMOVED
  else (slotStatusAt[s, t] = S_TAKEN)  => sem/PV_MOVED_BY_THIS
  else sem/PV_MOVED_OTHERWISE
}
/** The act-level view for the pending park: landed iff FREE. */
fun parkViewAt[s: Slot, t: Tick]: one sem/PeerView {
  (no slog/recordAt[s, t])            => sem/PV_ABSENT
  else (slotStatusAt[s, t] = S_RETIRED) => sem/PV_MOVED_OTHERWISE
  else (slotStatusAt[s, t] = S_FREE)   => sem/PV_MOVED_BY_THIS
  else sem/PV_UNMOVED
}
fact ClaimViews {
  all o: claim/ConfirmOcc + claim/ReleaseOcc       | o.peerView = slotViewAt[o.subject, o.tick]
  all o: claim/ActConfirmOcc + claim/ActReleaseOcc | o.peerView = parkViewAt[o.subject, o.tick]
}
/** takeOnlyByClaimants — THE EXCLUSIVE-ARM PREMISE (a named assumption, never a fact). */
pred takeOnlyByClaimants {
  all o: TakeOcc | committed[o] implies claim/phaseAt[o.subject, o.tick] = sem/I_RESERVED
}
/** parkOnlyUnderPendingAct — the CLOSE act is performed only under a pending park sub-intent
    (the runtime's "shelve is demand-only, and only inside the shelve leg"). */
pred parkOnlyUnderPendingAct {
  all o: ParkOcc | committed[o] implies claim/phaseAt[o.subject, o.tick] = sem/I_ACTING
}
/** THE LAW: under the premises, a TAKEN slot is claimed at every tick. */
pred takenSlotsAreClaimed {
  (takeOnlyByClaimants and parkOnlyUnderPendingAct) implies
    all s: Slot, t: Tick | slotStatusAt[s, t] = S_TAKEN implies some claim/holderAt[s, t]
}

// ── the havoc seeds (one kind per log) ─────────────────────────────────────────────────────────
/** Frame-free, always-committed seeds: an arbitrary well-formed slot record, an arbitrary
    well-formed claim record (any phase / holder / pending act). */
sig HavocSlotOcc  extends slog/SubjectOcc {} { bindings = subject }
sig HavocClaimOcc extends claim/IntentOcc {}  { bindings = subject }
fact HavocDiscipline {
  all h: HavocSlotOcc + HavocClaimOcc | h.admission = Accepted
  all h: HavocSlotOcc,  o: slog/SubjectOcc - HavocSlotOcc   | precedes[h.tick, o.tick]
  all h: HavocClaimOcc, o: claim/IntentOcc - HavocClaimOcc  | precedes[h.tick, o.tick]
}
pred seedAt[t: Tick] { some h: HavocSlotOcc + HavocClaimOcc | h.tick = t }

// ── the candidate inductive invariant (per-tick slice; the law itself is state-local) ──────────
pred e7Inv[t: Tick] {
  all s: Slot | slotStatusAt[s, t] = S_TAKEN implies claim/phaseAt[s, t] in sem/livePhases
}
pred lawSliceAt[t: Tick] {
  all s: Slot | slotStatusAt[s, t] = S_TAKEN implies some claim/holderAt[s, t]
}

// ── obligations ────────────────────────────────────────────────────────────────────────────────
assert e7_slice_faithful {
  (takeOnlyByClaimants and parkOnlyUnderPendingAct) implies
    ((all t: Tick | lawSliceAt[t]) iff takenSlotsAreClaimed)
}
assert e7_base { (takeOnlyByClaimants and parkOnlyUnderPendingAct and not seedAt[tord/first]) implies e7Inv[tord/first] }
assert e7_step {
  (takeOnlyByClaimants and parkOnlyUnderPendingAct) implies
    all t: Tick - tord/last | let t2 = tord/next[t] |
      (e7Inv[t] and not seedAt[t2]) implies e7Inv[t2]
}
assert e7_law { all t: Tick | e7Inv[t] implies lawSliceAt[t] }

// ── vacuity guards ─────────────────────────────────────────────────────────────────────────────
/** A seeded RESERVED claim beside a seeded FREE slot, with a later committed take: the step's
    legal path is realizable from seeded states. */
run e7_seeded_take {
  some hc: HavocClaimOcc, hs: HavocSlotOcc, k: TakeOcc |
    committed[hc] and claim/iPost[hc].iPhase = sem/I_RESERVED
    and committed[hs] and sPost[hs].sStat = S_FREE
    and committed[k] and k.subject = hc.subject and k.subject = hs.subject and precedes[hc.tick, k.tick] and precedes[hs.tick, k.tick]
    and takeOnlyByClaimants and parkOnlyUnderPendingAct
} for 5 but 5 Int, 2 Slot, 2 Owner, 2 Version, 6 Tick, 5 Occurrence, 8 Snapshot, 8 EntityId expect 1

/** A seeded TAKEN slot under a seeded HELD claim, with a later committed park under a pending
    act: the CLOSE path is realizable from seeded states. */
run e7_seeded_park {
  some hc: HavocClaimOcc, hs: HavocSlotOcc, a: claim/ActReserveOcc, p: ParkOcc |
    committed[hc] and claim/iPost[hc].iPhase = sem/I_HELD
    and committed[hs] and sPost[hs].sStat = S_TAKEN
    and committed[a] and committed[p] and a.subject = hc.subject and p.subject = hc.subject and hs.subject = hc.subject
    and precedes[hc.tick, a.tick] and precedes[hs.tick, a.tick] and precedes[a.tick, p.tick]
    and takeOnlyByClaimants and parkOnlyUnderPendingAct
} for 5 but 5 Int, 2 Slot, 2 Owner, 2 Version, 6 Tick, 5 Occurrence, 8 Snapshot, 8 EntityId expect 1

check e7_slice_faithful for 5 but 5 Int, 2 Slot, 2 Owner, 2 Version, 6 Tick, 6 Occurrence, 8 Snapshot, 8 EntityId expect 0
check e7_base           for 5 but 5 Int, 2 Slot, 2 Owner, 2 Version, 6 Tick, 6 Occurrence, 8 Snapshot, 8 EntityId expect 0
check e7_step           for 5 but 5 Int, 2 Slot, 2 Owner, 2 Version, 6 Tick, 6 Occurrence, 8 Snapshot, 8 EntityId expect 0
check e7_law            for 5 but 5 Int, 2 Slot, 2 Owner, 2 Version, 6 Tick, 6 Occurrence, 8 Snapshot, 8 EntityId expect 0

// ── W-scope escalation (the adoption gate: the unit-root trace window) ─────────────────────────
e7_step_w: check e7_step for 5 but 5 Int, 2 Slot, 2 Owner, 2 Version, 8 Tick, 8 Occurrence, 10 Snapshot, 8 EntityId expect 0
e7_law_w:  check e7_law  for 5 but 5 Int, 2 Slot, 2 Owner, 2 Version, 8 Tick, 8 Occurrence, 10 Snapshot, 8 EntityId expect 0

// ── supersession gate (b): richer entity scopes, trace window collapsed ────────────────────────
e7_step_s: check e7_step for 6 but 5 Int, 3 Slot, 3 Owner, 3 Version, 6 Tick, 6 Occurrence, 9 Snapshot, 10 EntityId expect 0
e7_law_s:  check e7_law  for 6 but 5 Int, 3 Slot, 3 Owner, 3 Version, 6 Tick, 6 Occurrence, 9 Snapshot, 10 EntityId expect 0
