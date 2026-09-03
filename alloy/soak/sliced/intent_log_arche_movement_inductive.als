module soak/sliced/intent_log_arche_movement_inductive

/*
 * E7 generalization ladder — the INTENT LOG's CITATION laws, MOVEMENT arm (DT-029 E1/E2 rung, SAMWISE): the
 * sibling of intent_log_arche_inductive for `sem/MoveSem` chains — one-shot movements whose CONFIRM frees the key
 * (`movementFreesKey`), so one subject accumulates MANY confirmed intents over time and law C must be stated per
 * CONFIRM occurrence, never on the head (DT-029 §3.3, MINESWEEPER's question). The additive peer is a Vat whose
 * level pours stack onto: the head cannot tell one pour from another — only the citation can. Laws A / B / C as in
 * the HOLD arm. ONE ARCHE PER LEG (SAMWISE-S1 as ruled; settled 2026-09-03 on MP 3.1's own words — "the caller's
 * context where there is one"): the inventory `transfer` COMPOSITE is one leg whose act touches two subjects
 * (`TransferIntent.other`): one call produced BOTH pours, so both carry the leg's origin (the destination is not
 * self-minted — it has a caller's context; and its own index entry keeps its idempotency independent of the
 * single-transaction boundary I3a had to flag as silently breakable). A distribute is N legs keyed on the member pools,
 * N origins, tied by the OWNER's saga (E3); plain legs cite one `OriginatorOcc`, the saga root's stand-in. Three
 * witnesses pin it: the composite (one leg, one origin on two vats), two legs on two vats sharing one ORIGIN, and two
 * legs of one saga on ONE subject (SPEARHEAD's discriminating case — commits under per-leg arche, would collide under
 * a per-saga one). THE SLICE'S OWN CHOICES: a pour cites the opener of its own vat's chain, or a composite leg whose
 * paired vat it is — anything else is refused `RForeignClaim`; a re-sent origin is refused `RDuplicateArche`; seeds cite nothing. A pour citing
 * a RELEASEd intent (the LATE ACT) is admitted — the chain reads FREE beside a moved-by-this view, the module's
 * `RD_LATE_ACT_ALERT` cell — and law B says it can never be CONFIRMed. Base-scope obligations by day; gates in a window.
 */

open meta/kernel
open meta/action/stateful
open meta/intent_log/semantics as sem
open meta/intent_log/intent_log[Vat, sem/MoveSem] as move
open meta/subject_log/subject_log[Vat, VatRec] as vlog
open meta/model_time/model_time as mt
open util/ordering[mt/Tick] as tord

// ── the peer: a Vat with its own log; pours stack; the citation's target is validated ───────────
sig Vat extends Scoped {}
fact VatRefs { all v: Vat | no v.dataRefs }
sig VatRec extends Snapshot { vLevel: one Int }
fact VatRecExtensional { all disj a, b: VatRec | a.vLevel != b.vLevel }

sig AddVatOcc extends vlog/SubjectOcc {} { bindings = subject }                      // genesis → level 0
sig PourOcc   extends vlog/SubjectOcc { amount: one Int } { bindings = subject + amount + arche }   // the additive act; cites its intent or nothing

fun vPre [o: vlog/SubjectOcc]: lone VatRec { o.pre  & VatRec }
fun vPost[o: vlog/SubjectOcc]: lone VatRec { o.post & VatRec }
fun vatLevelAt[v: Vat, t: Tick]: lone Int { vlog/recordAt[v, t].vLevel }

/** TransferIntent — the inventory `transfer` COMPOSITE: ONE leg whose act touches two subjects (source = `subject`,
    destination = `other`); one call produced both pours, so the destination's pour carries the same origin (MP 3.1:
    the caller's context where there is one) — idempotency of each write on its own index entry; adjacency (the
    inventory_pool model's `adjacentCommit`, one transaction) is a different relation and is not modelled here. */
sig TransferIntent in move/ReserveOcc { other: one Vat }
fact TransferPairs { all r: TransferIntent | r.other != r.subject }
/** OriginatorOcc — the saga root's stand-in (a row of the OWNER's log, outside both logs): what a plain leg's RESERVE cites. */
sig OriginatorOcc extends Action {} { no bindings }

one sig RVatStarted, RVatUnborn, RForeignClaim extends Reason {}
/** foreignPour — a citation that is neither this vat's committed opener nor a composite leg paired with this vat. */
pred foreignPour[o: PourOcc] {
  o.arche != o and o.arche != move/openerBefore[o.subject, o.tick]
  and not (o.arche in TransferIntent and (o.arche & TransferIntent).other = o.subject and committed[o.arche & TransferIntent])
}
fun addVatViol[o: AddVatOcc]: set Reason { (some vlog/priorOn[o]) => RVatStarted else none }
fun pourViol[o: PourOcc]: set Reason {
  ((no o.pre) => RVatUnborn else none)
  + (foreignPour[o] => RForeignClaim else none)
  + (vlog/archeDuplicate[o] => sem/RDuplicateArche else none)
}
fact VatAdmission {
  all o: AddVatOcc | (o.admission = Accepted iff no addVatViol[o]) and (o.admission in Rejected implies o.admission.because = addVatViol[o])
  all o: PourOcc   | (o.admission = Accepted iff no pourViol[o])   and (o.admission in Rejected implies o.admission.because = pourViol[o])
}
fact VatEffects {
  all o: AddVatOcc | committed[o] implies vPost[o].vLevel = 0
  all o: PourOcc   | committed[o] implies vPost[o].vLevel = plus[vPre[o].vLevel, o.amount]
}
fact VatSpine { vlog/chained and vlog/commitAlwaysAccepts and vlog/archeUniquePerSubject }
fact VatOrigins { all o: AddVatOcc | o.arche = o }

// ── the owner side: the movement chain over Vat, bindings, the adopted citation view + the residual ─
sig Owner extends Scoped {}
fact OwnerRefs { all o: Owner | no o.dataRefs }
sig Version {}
fact MoveSpine { move/spineAdopted }
fact MoveAttribution { move/citationView }   // DT-029 E2
fact MoveBindings {
  all o: move/HolderOcc  | o.holder in Owner.eId
  all o: move/ReserveOcc | o.ownerVersion in Version
  all o: move/CitingOcc  | o.peerRid in PourOcc
  all r: move/IntentRec  | r.iVersion in Version
  no move/ActReserveOcc and no move/TransferOcc   // MOVEMENT chains carry no sub-intents
  all o: move/IntentOcc  | o.arche != o implies o.arche in OriginatorOcc   // a leg's RESERVE cites the saga root, nothing else
  all o: OriginatorOcc   | o.admission = Accepted and o.arche = o
}
/** The residual for an additive peer: no "otherwise" (another owner's pour does not touch this intent) and vats
    are not minted by owners (no ABSENT) — an uncited view reads UNMOVED. */
fact MoveViews { all o: move/ViewOcc | not move/cited[o] implies o.peerView = sem/PV_UNMOVED }

// ── the three laws (premise-free), MOVEMENT arm ────────────────────────────────────────────────
fun openerAt[v: Vat, t: Tick]: lone move/IntentOcc {
  { r: move/IntentOcc | committed[r] and r.subject = v and notAfter[r.tick, t]
      and move/prePhase[r] in sem/freePhases and move/iPost[r].iPhase in sem/livePhases
      and no r2: move/IntentOcc | committed[r2] and r2.subject = v and precedes[r.tick, r2.tick] and notAfter[r2.tick, t]
                                   and move/prePhase[r2] in sem/freePhases and move/iPost[r2].iPhase in sem/livePhases }
}
fun poursCiting[v: Vat, i: move/IntentOcc]: set PourOcc { { x: PourOcc | committed[x] and x.subject = v and x.arche = i } }
/** poursCitingAt — the same, at-or-before `t` (never count a FUTURE pour in a per-tick invariant). */
fun poursCitingAt[v: Vat, i: move/IntentOcc, t: Tick]: set PourOcc { { x: poursCiting[v, i] | notAfter[x.tick, t] } }
/** THE COMPOSITE FINDING (first base run, law A and the step both): the module's citation view credits a CONFIRM from
    ANY citer, so a composite leg's CONFIRM on the source vat was credited by the destination's pour alone — a
    half-landed composite would confirm. The owner's discipline, the applier's fact: a committed CONFIRM settling a
    composite leg has a committed pour citing it on BOTH vats before it (the owner confirms on two replies). Plain legs
    have one subject and need nothing here; a distribute's wholeness is the OWNER's fold (E3), not a rule of this log. */
fact TransferConfirmedWhole {
  all o: move/ConfirmOcc | let i = move/settledIntent[o] | (committed[o] and i in TransferIntent) implies
    (some poursCitingAt[o.subject, i, o.tick] and some poursCitingAt[(i & TransferIntent).other, i, o.tick])
}
pred lawA {
  all o: move/ViewOcc | committed[o] implies
    ((o.peerView = sem/PV_MOVED_BY_THIS) iff (some x: poursCiting[o.subject, move/settledIntent[o]] | precedes[x.tick, o.tick]))
}
pred lawB {
  all o: move/ConfirmOcc | committed[o] implies
    (all x: poursCiting[o.subject, move/settledIntent[o]] | precedes[x.tick, o.tick] implies move/phaseAt[o.subject, x.tick] in sem/livePhases)
}
/** C, per CONFIRM and per SUBJECT — never on the head, which reads I_DONE (free) after a movement's CONFIRM. */
pred lawC {
  all o: move/ConfirmOcc | committed[o] implies one poursCiting[o.subject, move/settledIntent[o]]
}

// ── the havoc seeds ────────────────────────────────────────────────────────────────────────────
sig HavocVatOcc  extends vlog/SubjectOcc {} { bindings = subject }
sig HavocMoveOcc extends move/IntentOcc {}  { bindings = subject }
fact HavocDiscipline {
  all h: HavocVatOcc + HavocMoveOcc | h.admission = Accepted and h.arche = h
  all h: HavocVatOcc,  o: vlog/SubjectOcc - HavocVatOcc   | precedes[h.tick, o.tick]
  all h: HavocMoveOcc, o: move/IntentOcc - HavocMoveOcc   | precedes[h.tick, o.tick]
}
pred seedAt[t: Tick] { some h: HavocVatOcc + HavocMoveOcc | h.tick = t }

// ── the candidate inductive invariant (per-tick slice) ─────────────────────────────────────────
/** While a vat's chain is RESERVED, at most one pour on that vat cites its opener, each landed while RESERVED;
    once DONE (the movement confirmed), exactly one — per (opener, vat), so a transfer's paired vat is untouched. */
pred e7Inv[t: Tick] {
  all v: Vat | let i = openerAt[v, t] | {
    move/phaseAt[v, t] = sem/I_RESERVED implies
      (lone poursCitingAt[v, i, t] and all x: poursCitingAt[v, i, t] | move/phaseAt[v, x.tick] = sem/I_RESERVED)
    move/phaseAt[v, t] = sem/I_DONE implies
      (one poursCitingAt[v, i, t] and all x: poursCitingAt[v, i, t] | move/phaseAt[v, x.tick] = sem/I_RESERVED)
  }
}
pred lawSliceAt[t: Tick] {
  all v: Vat | let i = openerAt[v, t] | {
    move/phaseAt[v, t] = sem/I_DONE implies one poursCitingAt[v, i, t]
    all x: poursCitingAt[v, i, t] | move/phaseAt[v, t] in sem/I_RESERVED + sem/I_DONE implies move/phaseAt[v, x.tick] in sem/livePhases
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

// ── vacuity guards ─────────────────────────────────────────────────────────────────────────────
run e7_seeded_citedPour {
  some hm: HavocMoveOcc, hv: HavocVatOcc, p: PourOcc |
    committed[hm] and move/iPost[hm].iPhase = sem/I_RESERVED and committed[hv]
    and committed[p] and p.subject = hm.subject and p.subject = hv.subject and p.arche = hm
    and precedes[hm.tick, p.tick] and precedes[hv.tick, p.tick]
} for 5 but 5 Int, 2 Vat, 2 Owner, 2 Version, 6 Tick, 5 Occurrence, 8 Snapshot, 8 EntityId expect 1
run e7_seeded_uncitedPour {
  some hm: HavocMoveOcc, hv: HavocVatOcc, p: PourOcc |
    committed[hm] and move/iPost[hm].iPhase = sem/I_RESERVED and committed[hv]
    and committed[p] and p.subject = hm.subject and p.subject = hv.subject and p.arche = p
    and precedes[hm.tick, p.tick] and precedes[hv.tick, p.tick]
} for 5 but 5 Int, 2 Vat, 2 Owner, 2 Version, 6 Tick, 5 Occurrence, 8 Snapshot, 8 EntityId expect 1
run e7_seeded_foreignCite {
  some disj v1, v2: Vat, hm: HavocMoveOcc, hv: HavocVatOcc, p: PourOcc |
    committed[hm] and hm.subject = v1 and move/iPost[hm].iPhase = sem/I_RESERVED and committed[hv] and hv.subject = v2
    and p.subject = v2 and p.arche = hm and precedes[hm.tick, p.tick] and precedes[hv.tick, p.tick]
    and refusedAtAdmission[p] and p.admission.because = RForeignClaim
} for 5 but 5 Int, 2 Vat, 2 Owner, 2 Version, 6 Tick, 5 Occurrence, 8 Snapshot, 8 EntityId expect 1
/** C's antecedent under MOVEMENT: a committed CONFIRM whose key then reads I_DONE. */
run e7_seeded_confirmedMovement {
  some hm: HavocMoveOcc, hv: HavocVatOcc, p: PourOcc, f: move/ConfirmOcc |
    committed[hm] and move/iPost[hm].iPhase = sem/I_RESERVED and committed[hv]
    and committed[p] and committed[f] and p.subject = hm.subject and p.subject = hv.subject and f.subject = hm.subject
    and p.arche = hm and precedes[hm.tick, p.tick] and precedes[hv.tick, p.tick] and precedes[p.tick, f.tick]
    and move/phaseAt[f.subject, f.tick] = sem/I_DONE
} for 5 but 5 Int, 2 Vat, 2 Owner, 2 Version, 6 Tick, 5 Occurrence, 8 Snapshot, 8 EntityId expect 1
/** THE COMPOSITE: one leg, one origin on TWO subjects — the inventory `transfer` (S1's "two halves share one arche",
    right for the composite: the missing words were "one leg"). Pins uniqueness at per (arche, subject). */
run e7_seeded_compositeOneLegTwoSubjects {
  some disj v1, v2: Vat, r: TransferIntent, disj p1, p2: PourOcc |
    committed[r] and r.subject = v1 and r.other = v2
    and committed[p1] and committed[p2] and p1.subject = v1 and p2.subject = v2 and p1.arche = r and p2.arche = r
    and precedes[r.tick, p1.tick] and precedes[r.tick, p2.tick]
} for 6 but 5 Int, 2 Vat, 2 Owner, 2 Version, 7 Tick, 6 Occurrence, 9 Snapshot, 8 EntityId expect 1
/** ONE ORIGIN legitimately spanning TWO subjects at the INTENT-ROW level: two plain legs on two vats cite one originator,
    each with its own citing pour — where a shared origin lives under per-leg keying (never in the pool rows). */
run e7_seeded_twoLegsOneOrigin {
  some disj v1, v2: Vat, g: OriginatorOcc, disj r1, r2: move/ReserveOcc - TransferIntent, disj p1, p2: PourOcc |
    committed[g] and committed[r1] and committed[r2] and r1.subject = v1 and r2.subject = v2 and r1.arche = g and r2.arche = g
    and committed[p1] and committed[p2] and p1.subject = v1 and p2.subject = v2 and p1.arche = r1 and p2.arche = r2
    and precedes[g.tick, r1.tick] and precedes[g.tick, r2.tick] and precedes[r1.tick, p1.tick] and precedes[r2.tick, p2.tick]
} for 7 but 5 Int, 2 Vat, 2 Owner, 2 Version, 8 Tick, 7 Occurrence, 9 Snapshot, 8 EntityId expect 1
/** SPEARHEAD's DISCRIMINATING witness: two legs of ONE saga land on ONE subject, sequentially — both pours commit under
    per-leg arche (distinct leg ids on one vat); under a per-saga arche the second would collide. The only check that
    tells the two readings apart; every other check is blind to it. */
run e7_seeded_twoLegsOneSubject {
  some v: Vat, g: OriginatorOcc, disj r1, r2: move/ReserveOcc - TransferIntent, disj p1, p2: PourOcc, f: move/ConfirmOcc |
    committed[g] and committed[r1] and committed[p1] and committed[f] and committed[r2] and committed[p2]
    and r1.subject = v and r2.subject = v and p1.subject = v and p2.subject = v and f.subject = v
    and r1.arche = g and r2.arche = g and p1.arche = r1 and p2.arche = r2
    and precedes[g.tick, r1.tick] and precedes[r1.tick, p1.tick] and precedes[p1.tick, f.tick] and precedes[f.tick, r2.tick] and precedes[r2.tick, p2.tick]
} for 7 but 5 Int, 2 Vat, 2 Owner, 2 Version, 8 Tick, 7 Occurrence, 9 Snapshot, 8 EntityId expect 1
/** The LATE ACT is representable and B says it is never confirmed: a pour citing a RELEASEd intent lands on a free
    chain; the owner's view reads moved-by-this beside I_FREE — the module's RD_LATE_ACT_ALERT cell. */
run e7_seeded_lateAct {
  some hm: HavocMoveOcc, hv: HavocVatOcc, l: move/ReleaseOcc, p: PourOcc |
    committed[hm] and move/iPost[hm].iPhase = sem/I_RESERVED and committed[hv] and hv.subject = hm.subject
    and committed[l] and l.subject = hm.subject and precedes[hm.tick, l.tick]
    and committed[p] and p.subject = hm.subject and p.arche = hm and precedes[l.tick, p.tick] and precedes[hv.tick, p.tick]
    and move/redrive[move/phaseAt[p.subject, p.tick], sem/PV_MOVED_BY_THIS] = sem/RD_LATE_ACT_ALERT
} for 5 but 5 Int, 2 Vat, 2 Owner, 2 Version, 6 Tick, 5 Occurrence, 8 Snapshot, 8 EntityId expect 1

check e7_slice_faithful for 5 but 5 Int, 2 Vat, 2 Owner, 2 Version, 6 Tick, 6 Occurrence, 8 Snapshot, 8 EntityId expect 0
check e7_base           for 5 but 5 Int, 2 Vat, 2 Owner, 2 Version, 6 Tick, 6 Occurrence, 8 Snapshot, 8 EntityId expect 0
check e7_step           for 5 but 5 Int, 2 Vat, 2 Owner, 2 Version, 6 Tick, 6 Occurrence, 8 Snapshot, 8 EntityId expect 0
check e7_law_A          for 5 but 5 Int, 2 Vat, 2 Owner, 2 Version, 6 Tick, 6 Occurrence, 8 Snapshot, 8 EntityId expect 0
check e7_law_B          for 5 but 5 Int, 2 Vat, 2 Owner, 2 Version, 6 Tick, 6 Occurrence, 8 Snapshot, 8 EntityId expect 0
check e7_law_C          for 5 but 5 Int, 2 Vat, 2 Owner, 2 Version, 6 Tick, 6 Occurrence, 8 Snapshot, 8 EntityId expect 0

// ── census-widened and trace-collapsed gates — window only ─────────────────────────────────────
e7_step_w:  check e7_step  for 5 but 5 Int, 2 Vat, 2 Owner, 2 Version, 8 Tick, 8 Occurrence, 10 Snapshot, 8 EntityId expect 0
e7_law_w:   check e7_law_C for 5 but 5 Int, 2 Vat, 2 Owner, 2 Version, 8 Tick, 8 Occurrence, 10 Snapshot, 8 EntityId expect 0
e7_step_s:  check e7_step  for 6 but 5 Int, 3 Vat, 3 Owner, 3 Version, 6 Tick, 6 Occurrence, 9 Snapshot, 10 EntityId expect 0
e7_law_s:   check e7_law_C for 6 but 5 Int, 3 Vat, 3 Owner, 3 Version, 6 Tick, 6 Occurrence, 9 Snapshot, 10 EntityId expect 0
