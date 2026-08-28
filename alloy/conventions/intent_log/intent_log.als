module conventions/intent_log/intent_log

/*
 * CONVENTION EXEMPLAR — THE INTENT-LOG PATTERN (DT-027, SAMWISE; origin SPEARHEAD-D3, chartered by
 * MINESWEEPER-Q6, 2026-08-28). Canon: the demand cycle-claim log ruled for P3-I4 (chain A) and the
 * identity-keyed pool movements ruled in SAMWISE-S1 (chain B).
 *
 * THE CONVENTION: a module that must produce an effect in a PEER module's log ("two logs, one
 * fact") first appends RESERVE to an intent log it OWNS whose subject IS the contended peer
 * entity, acts on the peer ONCE (call-first), then appends CONFIRM (citing the peer's committed
 * row) or RELEASE (on the peer's TYPED refusal — never on a timeout). Competing intents are forks
 * on one chain; the peer keeps NO holder knowledge; recovery is the re-drive function of two heads
 * (meta/intent_log `redrive`). What the module `meta/intent_log/intent_log[Key, Sem]` cannot know
 * — and this exemplar shows — is the ATTRIBUTION LAW binding each CONFIRM / RELEASE's `peerView`
 * to the real peer head. It has two arms:
 *   - the EXCLUSIVE arm (HOLD chain): the peer act is a transition only a claimant can make
 *     (`take` on a free Cart), under the named PREMISE that only claimants perform it — then
 *     "peer moved" IS "moved by this intent";
 *   - the ADDITIVE arm (MOVEMENT chain): the peer act stacks (`pour` into a Vat) and the peer head
 *     cannot tell one pour from another — so the peer ROW carries the intent's identity
 *     (`movement` = the RESERVE it fulfils; the runtime's `movementId` column + partial unique
 *     index), a late pour citing a RELEASEd intent is DETECTABLE, and a reversal is itself a new
 *     movement intent naming the row it reverses (the detector excludes reversed rows).
 *
 * THE CAST: a Porter (owner) claims Carts (exclusive peer, HOLD) and pours into Vats (additive
 * peer, MOVEMENT). Carts and Vats keep their own logs and never mention porters. Both peers share
 * this file for compactness; in core models they live in DIFFERENT modules and the peer act is a
 * request/reply operation — the design doc carries the mapping.
 */

open meta/profiles/domain_log
open meta/kernel
open meta/subject_log/subject_log[Cart, CartRec] as clog
open meta/subject_log/subject_log[Vat, VatRec] as vlog
open meta/intent_log/semantics as sem              // aliased: the open-parameters below are qualified
open meta/intent_log/intent_log[Cart, sem/HoldSem] as claim   // chain 1: the cart CLAIM (HOLD)
open meta/intent_log/intent_log[Vat, sem/MoveSem]  as pour    // chain 2: the vat POUR (MOVEMENT)

// ── the owner ───────────────────────────────────────────────────────────────────────────────────
/** Porter — the owner: claims carts and pours into vats; identity only (its own log is elided —
    the exemplar reads the porter's holdings FROM THE CLAIM HEAD, the customer's law). */
sig Porter extends Scoped {}
fact PorterRefs { all p: Porter | no p.dataRefs }
/** PorterVersion — an opaque acting version of a porter (`owner_rid`). */
sig PorterVersion {}
/** cartsOf — THE HOLDER DERIVATION: a porter's carts are exactly the carts whose claim head
    names it. No membership record exists to drift. */
fun cartsOf[p: Porter, t: Tick]: set Cart { { c: Cart | claim/holderAt[c, t] = p.eId } }

// ── peer 1: the Cart (exclusive) ────────────────────────────────────────────────────────────────
abstract sig CartStatus {}
one sig C_FREE, C_TAKEN, C_RETIRED extends CartStatus {}
/** Cart — the exclusive peer: free / taken / retired; knows nothing about who took it. */
sig Cart extends Scoped {}
fact CartRefs { all c: Cart | no c.dataRefs }
sig CartRec extends Snapshot { cStat: one CartStatus }
fact CartRecExtensional { all disj a, b: CartRec | a.cStat != b.cStat }

sig AddCartOcc extends clog/SubjectOcc {} { bindings = subject }   // genesis → FREE
sig TakeOcc    extends clog/SubjectOcc {} { bindings = subject }   // FREE → TAKEN (the exclusive act)
sig ParkOcc    extends clog/SubjectOcc {} { bindings = subject }   // TAKEN → FREE (the inverse act)
sig RetireOcc  extends clog/SubjectOcc {} { bindings = subject }   // → RETIRED (a peer-side transition the owner cannot prevent)

fun cartStatusAt[c: Cart, t: Tick]: lone CartStatus { clog/recordAt[c, t].cStat }
fun cPre[o: clog/SubjectOcc]: lone CartRec { o.pre & CartRec }
fun cPost[o: clog/SubjectOcc]: lone CartRec { o.post & CartRec }

one sig RCartStarted, RCartUnborn, RCartBusy, RCartFree, RCartGone extends Reason {}
fun addCartViol[o: AddCartOcc]: set Reason { (some clog/priorOn[o]) => RCartStarted else none }
fun takeViol[o: TakeOcc]: set Reason {
  ((no o.pre) => RCartUnborn else none)
  + ((cPre[o].cStat = C_TAKEN) => RCartBusy else none)
  + ((cPre[o].cStat = C_RETIRED) => RCartGone else none)
}
fun parkViol[o: ParkOcc]: set Reason {
  ((no o.pre) => RCartUnborn else none)
  + ((cPre[o].cStat = C_FREE) => RCartFree else none)
  + ((cPre[o].cStat = C_RETIRED) => RCartGone else none)
}
fun retireViol[o: RetireOcc]: set Reason {
  ((no o.pre) => RCartUnborn else none) + ((cPre[o].cStat = C_RETIRED) => RCartGone else none)
}
fact CartAdmission {
  all o: AddCartOcc | (o.admission = Accepted iff no addCartViol[o]) and (o.admission in Rejected implies o.admission.because = addCartViol[o])
  all o: TakeOcc    | (o.admission = Accepted iff no takeViol[o])    and (o.admission in Rejected implies o.admission.because = takeViol[o])
  all o: ParkOcc    | (o.admission = Accepted iff no parkViol[o])    and (o.admission in Rejected implies o.admission.because = parkViol[o])
  all o: RetireOcc  | (o.admission = Accepted iff no retireViol[o])  and (o.admission in Rejected implies o.admission.because = retireViol[o])
}
fact CartEffects {
  all o: AddCartOcc | committed[o] implies cPost[o].cStat = C_FREE
  all o: TakeOcc    | committed[o] implies cPost[o].cStat = C_TAKEN
  all o: ParkOcc    | committed[o] implies cPost[o].cStat = C_FREE
  all o: RetireOcc  | committed[o] implies cPost[o].cStat = C_RETIRED
}
fact CartSpine { clog/chained and clog/commitAlwaysAccepts }

// ── peer 2: the Vat (additive) ──────────────────────────────────────────────────────────────────
/** Vat — the additive peer: a level that pours stack onto; the head cannot say who poured. */
sig Vat extends Scoped {}
fact VatRefs { all v: Vat | no v.dataRefs }
sig VatRec extends Snapshot { vLevel: one Int }
fact VatRecExtensional { all disj a, b: VatRec | a.vLevel != b.vLevel }

sig AddVatOcc extends vlog/SubjectOcc {} { bindings = subject }   // genesis → level 0
/** PourOcc — the additive act. `movement` is the intent identity the row carries (the runtime
    `movementId` = the RESERVE's rId); `reverses` names the pour this pour undoes, if any. */
sig PourOcc extends vlog/SubjectOcc { amount: one Int, movement: lone univ, reverses: lone univ }
  { bindings = subject + amount + movement + reverses }

fun vatLevelAt[v: Vat, t: Tick]: lone Int { vlog/recordAt[v, t].vLevel }
fun vPre[o: vlog/SubjectOcc]: lone VatRec { o.pre & VatRec }
fun vPost[o: vlog/SubjectOcc]: lone VatRec { o.post & VatRec }

one sig RVatStarted, RVatUnborn extends Reason {}
fun addVatViol[o: AddVatOcc]: set Reason { (some vlog/priorOn[o]) => RVatStarted else none }
fun pourViol[o: PourOcc]: set Reason { (no o.pre) => RVatUnborn else none }
fact VatAdmission {
  all o: AddVatOcc | (o.admission = Accepted iff no addVatViol[o]) and (o.admission in Rejected implies o.admission.because = addVatViol[o])
  all o: PourOcc   | (o.admission = Accepted iff no pourViol[o])   and (o.admission in Rejected implies o.admission.because = pourViol[o])
}
fact VatEffects {
  all o: AddVatOcc | committed[o] implies vPost[o].vLevel = 0
  all o: PourOcc   | committed[o] implies vPost[o].vLevel = plus[vPre[o].vLevel, o.amount]
}
fact VatSpine { vlog/chained and vlog/commitAlwaysAccepts }

// ── the two intent chains: spine adoption + owner-side bindings ─────────────────────────────────
fact ClaimSpine { claim/spineAdopted }
fact PourSpine  { pour/spineAdopted }
fact OwnerBindings {
  all o: claim/HolderOcc | o.holder in Porter.eId           // per instance: a union over two instances' `holder` is ambiguous (knowledge-base)
  all o: pour/HolderOcc  | o.holder in Porter.eId
  all o: claim/TransferOcc | o.from in Porter.eId and o.to in Porter.eId and o.toVersion in PorterVersion
  all o: claim/ReserveOcc | o.ownerVersion in PorterVersion
  all o: pour/ReserveOcc  | o.ownerVersion in PorterVersion
  all o: claim/CitingOcc | o.peerRid in clog/SubjectOcc
  all o: pour/CitingOcc  | o.peerRid in PourOcc
  all r: claim/IntentRec | r.iVersion in PorterVersion
  all r: pour/IntentRec  | r.iVersion in PorterVersion
  no claim/ActReserveOcc and no pour/ActReserveOcc and no pour/TransferOcc   // sub-intents are not this exemplar's subject
}

// ── ARM 1 — the EXCLUSIVE attribution (cart claim) ──────────────────────────────────────────────
/** takeOnlyByClaimants — THE EXCLUSIVE-ARM PREMISE (assume when: the peer act is performed only
    by owners holding a live reservation on the key — `accept` is demand-only). A NAMED
    ASSUMPTION, never a fact: a discipline breach (a bare `take`) stays representable. */
pred takeOnlyByClaimants {
  all o: TakeOcc | committed[o] implies claim/phaseAt[o.subject, o.tick] = sem/I_RESERVED
}
/** cartViewAt — the peer view of a cart relative to a claim: ABSENT before genesis, UNMOVED when
    free, MOVED_BY_THIS when taken (exclusive arm: under the premise the taker IS the claimant),
    MOVED_OTHERWISE when retired. */
fun cartViewAt[c: Cart, t: Tick]: one sem/PeerView {
  (no clog/recordAt[c, t])           => sem/PV_ABSENT
  else (cartStatusAt[c, t] = C_FREE)  => sem/PV_UNMOVED
  else (cartStatusAt[c, t] = C_TAKEN) => sem/PV_MOVED_BY_THIS
  else sem/PV_MOVED_OTHERWISE
}
/** The saga discipline: every claim CONFIRM / RELEASE reads the cart as it is at its tick. */
fact ClaimViews { all o: claim/ViewOcc | o.peerView = cartViewAt[o.subject, o.tick] }

// ── ARM 2 — the ADDITIVE attribution (vat pour) ─────────────────────────────────────────────────
/** reserveOf — the RESERVE a pour-chain CONFIRM / RELEASE settles: the latest committed RESERVE on
    the same vat before it (the chain has at most one live intent, so this is the one). */
fun reserveOf[o: pour/ViewOcc]: lone pour/ReserveOcc {
  { r: pour/ReserveOcc | committed[r] and r.subject = o.subject and precedes[r.tick, o.tick]
      and (no r2: pour/ReserveOcc | committed[r2] and r2.subject = o.subject
             and precedes[r.tick, r2.tick] and precedes[r2.tick, o.tick]) }
}
/** poursCiting — the committed pours on the vat carrying this intent's identity. */
fun poursCiting[r: pour/ReserveOcc]: set PourOcc {
  { p: PourOcc | committed[p] and p.subject = r.subject and p.movement = r }
}
/** The saga discipline for the additive arm: MOVED_BY_THIS iff a committed pour cites the
    reservation this occurrence settles; there is no "otherwise" for an additive peer (another
    owner's pour does not touch this intent), and vats are not minted by porters (no ABSENT). */
fact PourViews {
  all o: pour/ViewOcc |
    o.peerView = ((some p: poursCiting[reserveOf[o]] | precedes[p.tick, o.tick]) => sem/PV_MOVED_BY_THIS else sem/PV_UNMOVED)
}
/** The peer-row citation discipline (the runtime's `movementId` column + partial unique index):
    a pour's movement is a committed RESERVE on this vat that precedes it, and no two committed
    pours carry the same movement. */
fact MovementIdentity {
  all p: PourOcc | some p.movement implies
    (p.movement in pour/ReserveOcc and committed[p.movement & pour/ReserveOcc] and (p.movement & pour/ReserveOcc).subject = p.subject
     and precedes[(p.movement & pour/ReserveOcc).tick, p.tick])
  all disj p, q: PourOcc | (committed[p] and committed[q] and some p.movement) implies p.movement != q.movement
  all p: PourOcc | some p.reverses implies (p.reverses in PourOcc and committed[p.reverses & PourOcc] and (p.reverses & PourOcc).subject = p.subject
                                            and precedes[(p.reverses & PourOcc).tick, p.tick] and p.amount = minus[0, (p.reverses & PourOcc).amount])
}
/** lateAct — the DETECTOR: a committed pour whose movement's chain reads FREE at the pour's tick
    (the intent was RELEASEd before the act landed — rule R1 broken by a timeout read as a refusal),
    unless a committed reversal names it. */
pred lateAct[p: PourOcc] {
  committed[p] and some p.movement and pour/phaseAt[p.subject, p.tick] = sem/I_FREE
  and no q: PourOcc | committed[q] and q.reverses = p
}

// ── the exemplar's laws ─────────────────────────────────────────────────────────────────────────
/** takenCartsAreClaimed — under the exclusive-arm premise, a TAKEN cart is always held on the
    claim chain: the peer's exclusive state is credited to exactly the claim holder. */
pred takenCartsAreClaimed {
  takeOnlyByClaimants implies
    all c: Cart, t: Tick | cartStatusAt[c, t] = C_TAKEN implies some claim/holderAt[c, t]
}
/** holdingsReadTheHead — a porter's carts are exactly the claim heads naming it (definitional:
    there is no second record to disagree). */
pred holdingsReadTheHead {
  all p: Porter, c: Cart, t: Tick | (c in cartsOf[p, t]) iff claim/holderAt[c, t] = p.eId
}
/** confirmedPourCited — a committed pour CONFIRM's reservation has exactly one committed pour
    citing it (the additive arm's attribution + the unique index). */
pred confirmedPourCited {
  all o: pour/ConfirmOcc | committed[o] implies one poursCiting[reserveOf[o]]
}
/** releasedReserveUncited — under rule R1 (RELEASE only on a typed refusal, i.e. no pour landed),
    a committed pour RELEASE's reservation has no pour citing it BEFORE the release — a pour
    citing it AFTER is the late act the detector names. */
pred releasedReserveUncited {
  all o: pour/ReleaseOcc | committed[o] implies no p: poursCiting[reserveOf[o]] | precedes[p.tick, o.tick]
}
/** guarantees — the exemplar's promise. */
pred guarantees { takenCartsAreClaimed and holdingsReadTheHead and confirmedPourCited and releasedReserveUncited }
