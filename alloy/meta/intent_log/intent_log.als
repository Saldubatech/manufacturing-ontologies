module meta/intent_log/intent_log[Key, Sem]

/*
 * INTENT LOG — the reusable, verified core of the intent-log pattern (DT-027; ruled open by
 * MINESWEEPER-Q6, 2026-08-28; origin SPEARHEAD-D3). WHAT THIS OFFERS A DOMAIN MODELER (DT-013):
 * a module that must produce an effect in a PEER module's log first appends RESERVE to a log it
 * OWNS whose subject IS the contended peer entity (`Key`), acts on the peer once, then appends
 * CONFIRM (citing the peer's committed row) or RELEASE (on the peer's typed refusal). Competing
 * intents are forks on ONE chain, serialized by the spine's chaining law; crash recovery is the
 * RE-DRIVE function of two heads (the intent head, the peer head) — `redrive` below. The peer
 * keeps no holder knowledge; there is no cross-module transaction.
 *
 * PARAMETERS: `Key` — the contended entity (a kanban CardCycle, an InventoryPool, a DemandItem);
 * `Sem` — the CONFIRM semantics marker, `HoldSem` or `MoveSem` (meta/intent_log/semantics).
 * Each `open` gets its OWN chain spine (subject_log[Key, IntentRec]); a model may open several
 * (a HOLD chain and a MOVEMENT chain over different keys).
 *
 * WHAT STAYS WITH THE APPLYING MODULE (deliberately): the binding of `peerView` on CONFIRM /
 * RELEASE occurrences to the REAL peer head (the two-arm attribution law — exclusive transition
 * or additive row citing the intent's rId, DT-027 §7); the binding of `ownerVersion` / `peerRid`
 * / `act` (typed `univ` here) to its own occurrence atoms; the owner-side denormalization
 * (membership derived from the chain head); and the Shape-2 saga fold over several chains.
 *
 * Usage (chain A, the demand cycle claim):
 *   open meta/intent_log/intent_log[CardCycle, HoldSem] as claim
 *   fact ClaimSpine { claim/spineAdopted }
 *   fact ClaimAttribution { claim/citationView }   // moved-by-this = a peer row cites the intent (DT-029 E2)
 *   fact ClaimViews { all o: claim/ViewOcc | not claim/cited[o] implies o.peerView = cycleResidualOf[o.subject, o.tick] }
 *   fact ClaimVersions { all o: claim/ReserveOcc | o.ownerVersion in dlog/SubjectOcc }
 */

// BINDING CAVEAT (MINESWEEPER D2 review, point 2; SHRUNK by DT-029 E2): every law over `peerView`
// (confirmRequiresLanded, releaseRequiresUnlanded, subIntentReturnsToHold, redriveIdempotent) reads the
// view the applier bound. With `citationView` ADOPTED the moved-by-this half is DERIVED — a committed row
// outside this log cites the intent (`arche`, unforgeable) — and only the RESIDUAL split (absent / unmoved /
// moved-otherwise when NOT cited) is the applier's word, witnessed at its root; a wrong residual — a
// timeout read as a refusal — is exactly DT-027 §6's runtime residual.

open meta/kernel                                       // EntityId (the holder's identity)
open meta/action/stateful                              // Snapshot, StatefulAction, committed
open meta/model_time/model_time                        // Tick, precedes, notAfter
open meta/intent_log/semantics                         // Semantics, Phase, PeerView, RedriveAction, reasons
open meta/subject_log/subject_log[Key, IntentRec] as ilog   // the chain SPINE (chaining law, LOCF reads)

// ── the head record ─────────────────────────────────────────────────────────────────────────────
/** IntentRec — the chain's payload at one moment: the key's phase, its holder (the owner entity's
    identity), the owner's ACTING VERSION (`owner_rid` — how owner liveness is read from the owner's
    own log; DT-027 §4.1), and the pending sub-intent's act, if any. `iVersion` / `iAct` are typed
    `univ`: the applying module binds them to its own occurrence and act atoms. */
sig IntentRec extends IntentRecord {   // IntentRecord: the non-parametric parent every instance shares (semantics.als)
  iPhase:   one  Phase,
  iHolder:  lone EntityId,
  iVersion: lone univ,
  iAct:     lone univ,
  iMode:    lone ActMode
}
// Value semantics: a record IS its fields.
fact IntentRecExtensional {
  all disj a, b: IntentRec |
    a.iPhase != b.iPhase or a.iHolder != b.iHolder or a.iVersion != b.iVersion
    or a.iAct != b.iAct or a.iMode != b.iMode
}
// Well-formedness: a holder exactly in the live phases; a version exactly with a holder; an act
// and its mode exactly while ACTING.
fact IntentRecWellFormed {
  all r: IntentRec {
    (some r.iHolder)  iff r.iPhase in livePhases
    (some r.iVersion) iff some r.iHolder
    (some r.iAct)     iff r.iPhase = I_ACTING
    (some r.iMode)    iff r.iPhase = I_ACTING
  }
}

// ── the kinds (product-register names in comments; `holder` / `peerView` / `peerRid` declared ONCE
//    on abstract parents so union quantifiers stay unambiguous — the demand MemberOcc precedent) ───
/** IntentOcc — an occurrence on the intent chain of one key. */
abstract sig IntentOcc extends ilog/SubjectOcc {}
/** HolderOcc — a kind acting on behalf of ONE holder (every kind but TRANSFER). */
abstract sig HolderOcc extends IntentOcc { holder: one EntityId }
/** ViewOcc — a kind that carries what the owner READ of the peer head at its tick. */
abstract sig ViewOcc extends HolderOcc { peerView: one PeerView }
/** CitingOcc — a confirming kind: cites the peer's committed row (`peer_rid`). */
abstract sig CitingOcc extends ViewOcc { peerRid: one univ }

/** RESERVE — "I am about to act on this key", by the owner's acting version. */
sig ReserveOcc    extends HolderOcc { ownerVersion: one univ } { bindings = subject + holder + ownerVersion }
/** CONFIRM — the act landed: cite the peer row. HOLD: the custody opens; MOVEMENT: the key frees. */
sig ConfirmOcc    extends CitingOcc {}                       { bindings = subject + holder + peerView + peerRid }
/** RELEASE — the act did not land (typed refusal), or the hold ends. Never while moved-by-this (R1). */
sig ReleaseOcc    extends ViewOcc {}                         { bindings = subject + holder + peerView }
/** TRANSFER — the holder changes in ONE occurrence (HOLD only): never a holderless tick (SPEARHEAD-D5). */
sig TransferOcc   extends IntentOcc { from, to: one EntityId, toVersion: one univ }
                                                             { bindings = subject + from + to + toVersion }
/** ACT_RESERVE — a sub-intent: "I am about to perform `act` on the peer I hold" (HOLD only); `mode`
    says whether the act keeps the hold or closes it when confirmed. */
sig ActReserveOcc extends HolderOcc { act: one univ, mode: one ActMode }
                                                             { bindings = subject + holder + act + mode }
/** ACT_CONFIRM — the sub-intent's act landed: KEEP → the head reads as the hold again; CLOSE → the
    hold ends in this same occurrence (the key is FREE). */
sig ActConfirmOcc extends CitingOcc {}                       { bindings = subject + holder + peerView + peerRid }
/** ACT_RELEASE — the sub-intent's act did not land; the head reads as the hold again. */
sig ActReleaseOcc extends ViewOcc {}                         { bindings = subject + holder + peerView }

/** intentOccKinds — all kinds of this chain (alias-free for roots). */
fun intentOccKinds: set ilog/SubjectOcc { ilog/SubjectOcc }

// ── the read API ────────────────────────────────────────────────────────────────────────────────
/** iPre / iPost — an occurrence's records, TYPED (the DT-017 Snapshot field-name collision fix). */
fun iPre [o: ilog/SubjectOcc]: lone IntentRec { o.pre  & IntentRec }
fun iPost[o: ilog/SubjectOcc]: lone IntentRec { o.post & IntentRec }
/** recAt — LOCF of records: the key's intent record as of `t` (none before any history = FREE). */
fun recAt[k: Key, t: Tick]: lone IntentRec { ilog/recordAt[k, t] }
/** phaseAt — the key's phase as of `t`; a key with no history reads I_FREE. */
fun phaseAt[k: Key, t: Tick]: one Phase { some recAt[k, t] => recAt[k, t].iPhase else I_FREE }
/** holderAt — THE HOLDER DERIVATION: the holder is read from the chain head, never from a
    denormalized membership (customer brief D2.2). */
fun holderAt[k: Key, t: Tick]: lone EntityId { recAt[k, t].iHolder }
/** holderVersionAt — the acting version of the holder (owner liveness is read through it). */
fun holderVersionAt[k: Key, t: Tick]: lone univ { recAt[k, t].iVersion }
/** pendingActAt — the ONE pending sub-intent's act, if any. */
fun pendingActAt[k: Key, t: Tick]: lone univ { recAt[k, t].iAct }

// ── citation-derived attribution (DT-029 E2) — ADOPT `citationView` per instance ─────────────────
/** openerBefore / actOpenerBefore — THE INTENT A KEY IS UNDER, read kind-agnostically: the latest committed
    occurrence before `t` that took the key from a free phase into a live one (a RESERVE in every real trace;
    a seeded head in an E7 slice), and the latest one that took it from HELD into ACTING (an ACT_RESERVE).
    Kind-agnostic on purpose: the identity a callee cites is "the row that opened the intent", and a rung's
    havoc seed must be able to play that row or the ladder's seeded states could never satisfy the invariant. */
fun openerBefore[k: Key, t: Tick]: lone ilog/SubjectOcc {
  { r: ilog/SubjectOcc | committed[r] and r.subject = k and precedes[r.tick, t]
      and prePhase[r] in freePhases and iPost[r].iPhase in livePhases
      and no r2: ilog/SubjectOcc | committed[r2] and r2.subject = k and precedes[r.tick, r2.tick] and precedes[r2.tick, t]
                                    and prePhase[r2] in freePhases and iPost[r2].iPhase in livePhases }
}
fun actOpenerBefore[k: Key, t: Tick]: lone ilog/SubjectOcc {
  { a: ilog/SubjectOcc | committed[a] and a.subject = k and precedes[a.tick, t]
      and prePhase[a] = I_HELD and iPost[a].iPhase = I_ACTING
      and no a2: ilog/SubjectOcc | committed[a2] and a2.subject = k and precedes[a.tick, a2.tick] and precedes[a2.tick, t]
                                    and prePhase[a2] = I_HELD and iPost[a2].iPhase = I_ACTING }
}
/** settledIntent — the intent a view occurrence settles: the key's opener for CONFIRM / RELEASE, its act
    opener for ACT_CONFIRM / ACT_RELEASE (the LEVEL rule: an act's peer row cites the ACT_RESERVE — its
    immediate caller). */
fun settledIntent[o: ViewOcc]: lone ilog/SubjectOcc {
  (o in ActConfirmOcc + ActReleaseOcc) => actOpenerBefore[o.subject, o.tick] else openerBefore[o.subject, o.tick]
}
/** citers — the committed PEER rows whose origin (`arche`) is `i`: every committed Action outside EVERY intent
    chain's rows (`intentRows`: a row whose records are `IntentRecord`s — structural, no free marker set). Under the immediate-caller rule these are
    exactly the peer rows the intent caused (a refused peer row is not committed; a peer's own follow-ups cite the
    peer row; saga legs cite the ORIGINATOR). Intent rows are excluded because an owner-side row may legally cite a
    cited row on its own chain (E1) and a SIBLING chain's RESERVE may cite this one (nested intents) — neither is
    the peer act (the E2 self-check found both). `some x.arche` keeps an empty `i` from matching uncited rows. */
/** intentRows — every committed row of ANY intent chain, recognized structurally: its records are IntentRecords. */
fun intentRows: set Action { { a: StatefulAction | some ((a.pre + a.post) & IntentRecord) } }
fun citers[i: ilog/SubjectOcc]: set Action { { x: Action - intentRows | committed[x] and some x.arche and x.arche = i } }
/** cited — the intent `o` settles has a citer committed before `o`. */
pred cited[o: ViewOcc] { some x: citers[settledIntent[o]] | precedes[x.tick, o.tick] }
/** citedAt / actCitedAt — the tick-level readings (probes, view functions): the key's latest RESERVE /
    ACT_RESERVE (opener / act opener) before `t` has a citer at-or-before `t`. */
pred citedAt[k: Key, t: Tick]    { some x: citers[openerBefore[k, t]]    | notAfter[x.tick, t] }
pred actCitedAt[k: Key, t: Tick] { some x: citers[actOpenerBefore[k, t]] | notAfter[x.tick, t] }
/** citationView — THE ATTRIBUTION LAW's derivable half (ADOPT as a fact per instance, like `spineAdopted`
    and `subject_log`'s `archeUniquePerSubject`): the owner reads the peer as moved-by-this exactly when a
    committed row outside this log cites the intent being settled. The RESIDUAL split — ABSENT / UNMOVED /
    MOVED_OTHERWISE when NOT cited — stays the applier's fact, witnessed at its root (DT-029 D-2). No guard
    or law changes: `confirmRequiresLanded` / `releaseRequiresUnlanded` now read "a CONFIRM is cited, a
    RELEASE is not". Adopted, not global, because the module's own suite binds the view freely to test
    guards, effects and re-drive with no peer domain at all. */
pred citationView { all o: ViewOcc | (o.peerView = PV_MOVED_BY_THIS) iff cited[o] }
/** closingAct — an ACT_CONFIRM whose sub-intent was reserved in CLOSE mode: it ends the hold. */
pred closingAct[o: ilog/SubjectOcc] { o in ActConfirmOcc and iPre[o].iMode = AM_CLOSE }
/** liveAt / heldAt — the key is taken / a hold is in force as of `t`. */
pred liveAt[k: Key, t: Tick] { phaseAt[k, t] in livePhases }
pred heldAt[k: Key, t: Tick] { phaseAt[k, t] in heldPhases }
/** isHold — this chain was instantiated with HOLD semantics (read through the `holdSemantics` set —
    see semantics.als for why not `Sem in HoldSem`). */
pred isHold { Sem in holdSemantics }

// ── admission (reason-precise, per kind — the reason_precise_refusals idiom) ────────────────────
fun prePhase[o: ilog/SubjectOcc]: one Phase { some iPre[o] => iPre[o].iPhase else I_FREE }
fun wrongHolder[o: HolderOcc]: set Reason {
  (some iPre[o].iHolder and iPre[o].iHolder != o.holder) => RWrongHolder else none
}

fun reserveViol[o: ReserveOcc]: set Reason { (prePhase[o] not in freePhases) => RKeyTaken else none }
fun confirmViol[o: ConfirmOcc]: set Reason {
  ((prePhase[o] != I_RESERVED) => RNotReserved else none)
  + wrongHolder[o]
  + ((o.peerView != PV_MOVED_BY_THIS) => RNotLanded else none)
}
fun releaseViol[o: ReleaseOcc]: set Reason {
  ((prePhase[o] not in I_RESERVED + I_HELD) => ((prePhase[o] = I_ACTING) => RActPending else RNotReserved) else none)
  + wrongHolder[o]
  + ((o.peerView = PV_MOVED_BY_THIS) => RLanded else none)
}
fun transferViol[o: TransferOcc]: set Reason {
  ((not isHold) => RNotHoldSemantics else none)
  + ((prePhase[o] != I_HELD) => ((prePhase[o] = I_ACTING) => RActPending else RNotHeld) else none)
  + ((some iPre[o].iHolder and iPre[o].iHolder != o.from) => RWrongHolder else none)
}
fun actReserveViol[o: ActReserveOcc]: set Reason {
  ((not isHold) => RNotHoldSemantics else none)
  + ((prePhase[o] != I_HELD) => ((prePhase[o] = I_ACTING) => RActPending else RNotHeld) else none)
  + wrongHolder[o]
}
fun actConfirmViol[o: ActConfirmOcc]: set Reason {
  ((prePhase[o] != I_ACTING) => RNoActPending else none)
  + wrongHolder[o]
  + ((o.peerView != PV_MOVED_BY_THIS) => RNotLanded else none)
}
fun actReleaseViol[o: ActReleaseOcc]: set Reason {
  ((prePhase[o] != I_ACTING) => RNoActPending else none)
  + wrongHolder[o]
  + ((o.peerView = PV_MOVED_BY_THIS) => RLanded else none)
}

fact AdmissionWitness {
  all o: ReserveOcc    | (o.admission = Accepted iff no reserveViol[o])    and (o.admission in Rejected implies o.admission.because = reserveViol[o])
  all o: ConfirmOcc    | (o.admission = Accepted iff no confirmViol[o])    and (o.admission in Rejected implies o.admission.because = confirmViol[o])
  all o: ReleaseOcc    | (o.admission = Accepted iff no releaseViol[o])    and (o.admission in Rejected implies o.admission.because = releaseViol[o])
  all o: TransferOcc   | (o.admission = Accepted iff no transferViol[o])   and (o.admission in Rejected implies o.admission.because = transferViol[o])
  all o: ActReserveOcc | (o.admission = Accepted iff no actReserveViol[o]) and (o.admission in Rejected implies o.admission.because = actReserveViol[o])
  all o: ActConfirmOcc | (o.admission = Accepted iff no actConfirmViol[o]) and (o.admission in Rejected implies o.admission.because = actConfirmViol[o])
  all o: ActReleaseOcc | (o.admission = Accepted iff no actReleaseViol[o]) and (o.admission in Rejected implies o.admission.because = actReleaseViol[o])
}

// ── effects (committed) — per-kind frames ───────────────────────────────────────────────────────
fact EffectWitness {
  all o: ReserveOcc | committed[o] implies {
    iPost[o].iPhase = I_RESERVED and iPost[o].iHolder = o.holder
    and iPost[o].iVersion = o.ownerVersion and no iPost[o].iAct
  }
  all o: ConfirmOcc | committed[o] implies {
    isHold => (iPost[o].iPhase = I_HELD and iPost[o].iHolder = o.holder
               and iPost[o].iVersion = iPre[o].iVersion and no iPost[o].iAct)
           else (iPost[o].iPhase = I_DONE and no iPost[o].iHolder)
  }
  all o: ReleaseOcc    | committed[o] implies (iPost[o].iPhase = I_FREE and no iPost[o].iHolder)
  all o: TransferOcc   | committed[o] implies {
    iPost[o].iPhase = I_HELD and iPost[o].iHolder = o.to and iPost[o].iVersion = o.toVersion and no iPost[o].iAct
  }
  all o: ActReserveOcc | committed[o] implies {
    iPost[o].iPhase = I_ACTING and iPost[o].iHolder = o.holder
    and iPost[o].iVersion = iPre[o].iVersion and iPost[o].iAct = o.act and iPost[o].iMode = o.mode
  }
  all o: ActConfirmOcc | committed[o] implies {
    closingAct[o] => (iPost[o].iPhase = I_FREE and no iPost[o].iHolder)
                else (iPost[o].iPhase = I_HELD and iPost[o].iHolder = o.holder
                      and iPost[o].iVersion = iPre[o].iVersion and no iPost[o].iAct)
  }
  all o: ActReleaseOcc | committed[o] implies {
    iPost[o].iPhase = I_HELD and iPost[o].iHolder = o.holder
    and iPost[o].iVersion = iPre[o].iVersion and no iPost[o].iAct
  }
}

/** spineAdopted — the spine's chaining law + the v1 result policy; the APPLYING module adopts it
    as a fact (`fact ClaimSpine { claim/spineAdopted }`), exactly as subject_log consumers do. */
pred spineAdopted { ilog/chained and ilog/commitAlwaysAccepts }

// ── the re-drive function of two heads (DT-027 §6) — TOTAL over (phase × peer view) ─────────────
/** redrive — the one action a (intent phase, peer view) pair prescribes. Its VERDICT depends on
    the two heads only (actor-independent); its EXECUTION is owner-restricted in the
    RD_OWNER_REDRIVE cells (rule R2). Under HOLD, a FREE key beside a moved-by-this peer is not
    definable (exclusive arm); under MOVEMENT it is the detectable late act (additive arm). */
fun redrive[ph: Phase, v: PeerView]: one RedriveAction {
  (ph in freePhases) => (
      (v = PV_MOVED_BY_THIS and ph = I_FREE) => (isHold => RD_NOT_DEFINABLE else RD_LATE_ACT_ALERT)
      else RD_SETTLED)
  else (ph = I_RESERVED) => (
      (v = PV_UNMOVED)         => RD_OWNER_REDRIVE
      else (v = PV_ABSENT)     => (isHold => RD_GENESIS else RD_NOT_DEFINABLE)   // genesis legs are HOLD (custody) chains
      else (v = PV_MOVED_BY_THIS) => RD_CONFIRM
      else RD_RELEASE)
  else (ph = I_HELD) => (
      (v = PV_UNMOVED)         => RD_OWNER_REDRIVE
      else (v = PV_MOVED_BY_THIS) => RD_SETTLED
      else RD_RELEASE_DETACH)
  else (
      (v = PV_UNMOVED)         => RD_OWNER_REDRIVE
      else (v = PV_ABSENT)     => RD_NOT_DEFINABLE
      else (v = PV_MOVED_BY_THIS) => RD_ACT_CONFIRM
      else RD_ACT_RELEASE)
}

// ── the published laws (named predicates; law cards LC-IL-NN in the workbook) ───────────────────
/** reserveReadsFree — EXCLUSIVITY AS A THEOREM OF THE CHAIN GUARD: a committed RESERVE read a
    free key. Two racing reservations are two appends on one head; the loser is refused
    RKeyTaken before the peer is touched. No membership table is consulted. */
pred reserveReadsFree { all o: ReserveOcc | committed[o] implies prePhase[o] in freePhases }
/** reservationsSeparatedByFreeing — EXCLUSIVITY WITHOUT THE ADMISSION VOCABULARY (MINESWEEPER D2
    review, point 1): two committed reservations on one key are separated by a committed occurrence
    that left the key free (a RELEASE, a movement's CONFIRM, or a closing act's confirmation). Stated
    over kinds and effects only, so a later edit to `reserveViol` cannot silently weaken exclusivity. */
pred reservationsSeparatedByFreeing {
  all disj a, b: ReserveOcc | (committed[a] and committed[b] and a.subject = b.subject and precedes[a.tick, b.tick]) implies
    (some f: intentOccKinds | committed[f] and f.subject = a.subject and precedes[a.tick, f.tick] and precedes[f.tick, b.tick]
       and iPost[f].iPhase in freePhases)
}
/** oneLiveHolderPerKey — at any tick a key has at most one holder, and a holder exactly while live. */
pred oneLiveHolderPerKey {
  all k: Key, t: Tick | lone holderAt[k, t] and ((some holderAt[k, t]) iff liveAt[k, t])
}
/** confirmRequiresLanded — a committed CONFIRM / ACT_CONFIRM read the peer as moved-by-this. */
pred confirmRequiresLanded { all o: CitingOcc | committed[o] implies o.peerView = PV_MOVED_BY_THIS }
/** releaseRequiresUnlanded — RULE R1 as a guard theorem: no committed RELEASE / ACT_RELEASE read the
    peer as moved-by-this (release only on a typed refusal, or after the compensating act). */
pred releaseRequiresUnlanded {
  all o: ReleaseOcc + ActReleaseOcc | committed[o] implies o.peerView != PV_MOVED_BY_THIS
}
/** holdPersistsUntilRelease — HOLD: while a key is held, only RELEASE, TRANSFER, or a CLOSING
    sub-intent's confirmation changes the holder; every other committed occurrence keeps holder
    and hold. */
pred holdPersistsUntilRelease {
  all o: intentOccKinds - (ReleaseOcc + TransferOcc) |
    (committed[o] and prePhase[o] in heldPhases and not closingAct[o]) implies
      (iPost[o].iPhase in heldPhases and iPost[o].iHolder = iPre[o].iHolder)
}
/** movementFreesKey — MOVEMENT: a committed CONFIRM leaves the key available (I_DONE, no holder). */
pred movementFreesKey {
  (not isHold) implies all o: ConfirmOcc | committed[o] implies iPost[o].iPhase = I_DONE
}
/** transferAtomic — a committed TRANSFER moves the hold from `from` to `to` in ONE occurrence:
    held before, held after, never a holderless tick in between (SPEARHEAD-D5 hand-over). */
pred transferAtomic {
  all o: TransferOcc | committed[o] implies
    (prePhase[o] = I_HELD and iPre[o].iHolder = o.from and iPost[o].iPhase = I_HELD and iPost[o].iHolder = o.to)
}
/** subIntentReturnsToHold — DT-027 §5 invariant (a): after a settled sub-intent the head reads
    as the hold again (same holder, phase I_HELD) — or, for a CLOSING act confirmed, as FREE in
    that same occurrence (no intermediate "held, peer gone back" tick). */
pred subIntentReturnsToHold {
  all o: ActReleaseOcc | committed[o] implies
    (iPost[o].iPhase = I_HELD and iPost[o].iHolder = iPre[o].iHolder)
  all o: ActConfirmOcc | committed[o] implies
    (closingAct[o] => iPost[o].iPhase = I_FREE
                 else (iPost[o].iPhase = I_HELD and iPost[o].iHolder = iPre[o].iHolder))
}
/** oneSubIntentPerKey — DT-027 §5 invariant (b): at most one pending sub-intent per key, and a
    committed ACT_RESERVE read the plain hold (never a pending sub-intent). */
pred oneSubIntentPerKey {
  all k: Key, t: Tick | lone pendingActAt[k, t]
  all o: ActReserveOcc | committed[o] implies prePhase[o] = I_HELD
}
/** subIntentsRequireHold — sub-intents and TRANSFER commit only on HOLD chains. */
pred subIntentsRequireHold {
  (not isHold) implies no o: ActReserveOcc + TransferOcc | committed[o]
}
/** redriveTotal — every (phase, peer view) pair prescribes exactly one action. */
pred redriveTotal { all ph: Phase, v: PeerView | one redrive[ph, v] }
/** redriveIdempotent — after a re-drive action's own append, the pair is settled: CONFIRM at the
    view that justified it; RELEASE at any view it was admitted with; ACT_CONFIRM and ACT_RELEASE
    at the hold's own view (moved-by-this: the peer is still held). */
pred redriveIdempotent {
  all o: ConfirmOcc    | committed[o] implies redrive[iPost[o].iPhase, PV_MOVED_BY_THIS] = RD_SETTLED
  all o: ReleaseOcc    | committed[o] implies redrive[iPost[o].iPhase, o.peerView] = RD_SETTLED
  all o: ActReleaseOcc | committed[o] implies redrive[iPost[o].iPhase, PV_MOVED_BY_THIS] = RD_SETTLED
  all o: ActConfirmOcc | committed[o] implies
    (closingAct[o] => redrive[iPost[o].iPhase, PV_UNMOVED] = RD_SETTLED
                 else redrive[iPost[o].iPhase, PV_MOVED_BY_THIS] = RD_SETTLED)
}

/** guarantees — the module's full promise: the conjunction of the published laws (structural
    laws — holder derivation reads the head, recorded-axis-only ordering, verdict
    actor-independence — hold by construction and are carded, not checked). */
pred guarantees {
  reserveReadsFree
  and reservationsSeparatedByFreeing
  and oneLiveHolderPerKey
  and confirmRequiresLanded
  and releaseRequiresUnlanded
  and holdPersistsUntilRelease
  and movementFreesKey
  and transferAtomic
  and subIntentReturnsToHold
  and oneSubIntentPerKey
  and subIntentsRequireHold
  and redriveTotal
  and redriveIdempotent
}
