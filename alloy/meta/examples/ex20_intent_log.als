module meta/examples/ex20_intent_log

open meta/kernel
open meta/action/stateful
open meta/subject_log/subject_log[LuggageCart, LuggageCartState] as lcart
open meta/intent_log/semantics as sem                       // aliased: pass sem/HoldSem below (the diamond rule)
open meta/intent_log/intent_log[LuggageCart, sem/HoldSem] as claim

/*
 * ex20 — THE INTENT LOG (meta/intent_log, DT-027): "two logs, one fact" without a cross-module
 * transaction. Hotel flavor: a BELLHOP needs a LUGGAGE CART that the concierge desk's cart log
 * owns. The bellhop's module never edits the cart log and the cart log never learns who holds a
 * cart; instead the bellhop RESERVEs the cart on a claim log it owns (keyed by the cart), asks the
 * desk to CHECK OUT the cart (one call), then CONFIRMs (citing the desk's row) or RELEASEs on a
 * typed refusal. Two bellhops racing for one cart fork on the claim chain — the loser is refused
 * before the desk is called. After a crash the two heads say what to do (`claim/redrive`).
 *
 * Pattern: intent log (reserve → act → confirm/release; re-drive = f(intent head, peer head)).
 * UML: saga with a reservation step; FP: a two-phase effect with an idempotent recovery function.
 * Use-when: an exclusive or non-idempotent effect on a PEER module's entity, with contention.
 * Avoid: idempotent, uncontended legs (a re-gate is cheaper); single-module state (that is a lock).
 * See-also: ex19 (the spine the chain rides), conventions/intent_log (both attribution arms),
 *           conventions/call_first_saga (the call-first shape the act follows).
 *
 * RECIPE (what you copy for a real module):
 *   1. open meta/intent_log/semantics as sem ; open meta/intent_log/intent_log[PeerEntity, sem/HoldSem] as claim
 *   2. fact { claim/spineAdopted }
 *   3. bind the opaque fields: holder ∈ your owner's eId, ownerVersion ∈ your owner's occurrences, peerRid ∈ the peer's occurrences
 *   4. the ATTRIBUTION law: `all o: claim/ViewOcc | o.peerView = <your view of the peer head at o.tick>`
 *   5. read holdings FROM THE HEAD: claim/holderAt[peer, t] — never from a membership copy
 *   6. recover with claim/redrive[claim/phaseAt[peer, t], <view>] — the same function for the saga and the probe
 */

// ── the peer: the desk's cart log (knows nothing about bellhops) ────────────────────────────────
abstract sig CartAvail {}
one sig IN_RACK, CHECKED_OUT extends CartAvail {}
sig LuggageCart extends Scoped {}
fact LuggageCartRefs { all c: LuggageCart | no c.dataRefs }
sig LuggageCartState extends Snapshot { avail: one CartAvail }
fact LuggageCartStateExtensional { all disj a, b: LuggageCartState | a.avail != b.avail }

sig RackOcc     extends lcart/SubjectOcc {} { bindings = subject }   // genesis / return → IN_RACK
sig CheckOutOcc extends lcart/SubjectOcc {} { bindings = subject }   // IN_RACK → CHECKED_OUT (the exclusive act)
one sig RCartOut extends Reason {}
fun checkOutViol[o: CheckOutOcc]: set Reason { ((o.pre & LuggageCartState).avail = CHECKED_OUT) => RCartOut else none }
fact CartWitnessing {
  all o: RackOcc     | o.admission = Accepted
  all o: CheckOutOcc | (o.admission = Accepted iff no checkOutViol[o]) and (o.admission in Rejected implies o.admission.because = checkOutViol[o])
}
fact CartEffects {
  all o: RackOcc     | committed[o] implies (o.post & LuggageCartState).avail = IN_RACK
  all o: CheckOutOcc | committed[o] implies (o.post & LuggageCartState).avail = CHECKED_OUT
}
fact CartSpine { lcart/chained and lcart/commitAlwaysAccepts }
fun availAt[c: LuggageCart, t: Tick]: lone CartAvail { lcart/recordAt[c, t].avail }

// ── the owner: a bellhop, whose carts are READ from the claim head ──────────────────────────────
sig Bellhop extends Scoped {}
fact BellhopRefs { all b: Bellhop | no b.dataRefs }
sig Shift {}   // the bellhop's acting version (owner_rid), opaque here
fun cartsOf[b: Bellhop, t: Tick]: set LuggageCart { { c: LuggageCart | claim/holderAt[c, t] = b.eId } }

fact ClaimSpine { claim/spineAdopted }
fact ClaimBindings {
  all o: claim/HolderOcc  | o.holder in Bellhop.eId
  all o: claim/ReserveOcc | o.ownerVersion in Shift
  all o: claim/CitingOcc  | o.peerRid in CheckOutOcc
  all o: claim/TransferOcc | o.from in Bellhop.eId and o.to in Bellhop.eId and o.toVersion in Shift
  all r: claim/IntentRec  | r.iVersion in Shift
  no claim/ActReserveOcc
}
/** THE ATTRIBUTION LAW (exclusive arm): checked out = moved by this claim, under the premise that
    only claimants check carts out. */
pred checkOutOnlyByClaimants {
  all o: CheckOutOcc | committed[o] implies claim/phaseAt[o.subject, o.tick] = sem/I_RESERVED
}
fun viewAt[c: LuggageCart, t: Tick]: one sem/PeerView {
  (no lcart/recordAt[c, t]) => sem/PV_ABSENT
  else (availAt[c, t] = IN_RACK) => sem/PV_UNMOVED else sem/PV_MOVED_BY_THIS
}
fact ClaimViews { all o: claim/ViewOcc | o.peerView = viewAt[o.subject, o.tick] }

// ── the story: reserve → check out → confirm; the bellhop holds the cart, read from the head ─────
run ex20_claimStory {
  some b: Bellhop, c: LuggageCart, r: claim/ReserveOcc, k: CheckOutOcc, f: claim/ConfirmOcc | {
    committed[r] and committed[k] and committed[f]
    r.subject = c and k.subject = c and f.subject = c and r.holder = b.eId and f.holder = b.eId
    precedes[r.tick, k.tick] and precedes[k.tick, f.tick]
    c in cartsOf[b, f.tick]
    checkOutOnlyByClaimants
  }
} for 5 but 5 Int, 2 Bellhop, 1 LuggageCart, 2 Shift, 7 Tick, 6 Occurrence, 8 Snapshot, 8 EntityId expect 1

// ── the race: the second bellhop is refused on the claim chain BEFORE the desk is called ────────
run ex20_raceLoserRefused {
  some c: LuggageCart, disj a, b: claim/ReserveOcc | {
    committed[a] and refusedAtAdmission[b] and b.admission.because = sem/RKeyTaken
    a.subject = c and b.subject = c and a.holder != b.holder and precedes[a.tick, b.tick]
  }
} for 5 but 5 Int, 2 Bellhop, 1 LuggageCart, 2 Shift, 6 Tick, 5 Occurrence, 7 Snapshot, 8 EntityId expect 1

// ── the crash: checked out, confirm lost — the two heads prescribe CONFIRM, not a second check-out ─
run ex20_lostAckRedrive {
  some c: LuggageCart, r: claim/ReserveOcc, k: CheckOutOcc, t: Tick | {
    committed[r] and committed[k] and r.subject = c and k.subject = c and precedes[r.tick, k.tick]
    no f: claim/ConfirmOcc | committed[f]
    notAfter[k.tick, t] and claim/redrive[claim/phaseAt[c, t], viewAt[c, t]] = sem/RD_CONFIRM
    checkOutOnlyByClaimants
  }
} for 5 but 5 Int, 1 Bellhop, 1 LuggageCart, 1 Shift, 6 Tick, 5 Occurrence, 7 Snapshot, 6 EntityId expect 1

// ── the theorem: a checked-out cart is always some bellhop's, read from the claim head ──────────
assert ex20_checkedOutIsHeld {
  checkOutOnlyByClaimants implies
    all c: LuggageCart, t: Tick | availAt[c, t] = CHECKED_OUT implies some claim/holderAt[c, t]
}
check ex20_checkedOutIsHeld for 5 but 5 Int, 2 Bellhop, 2 LuggageCart, 2 Shift, 6 Tick, 6 Occurrence, 8 Snapshot, 10 EntityId expect 0
