module meta/intent_log/tests/intent_log

/*
 * Suite for the INTENT LOG (DT-027, SAMWISE), exercised on two minimal local instantiations:
 * a HOLD chain over `Peg` (the pattern's chain A/C shape — custody, TRANSFER, sub-intents) and a
 * MOVEMENT chain over `Slab` (chain B-mov — one-shot movements that free the key). Holders are
 * `Owner` entities; owner versions, peer rIds, and acts are opaque local atoms (the applying
 * module binds them to its own occurrences). Verifies exactly what the module OWNS: the guard
 * theorems (exclusivity, R1), the effect frames (hold persistence, movement freeing, atomic
 * transfer, sub-intent invariants (a)/(b)), and the re-drive function's totality and idempotence.
 * Command prefix `unit_il_*`.
 */

open meta/kernel
open meta/action/stateful
open meta/intent_log/semantics as sem   // aliased: open-parameters below must be QUALIFIED (the DT-024 diamond rule)
open meta/intent_log/intent_log[Peg, sem/HoldSem]  as hold
open meta/intent_log/intent_log[Slab, sem/MoveSem] as move

// ── the local cast ──────────────────────────────────────────────────────────────────────────────
/** Peg — a contended resource under HOLD semantics (a cycle, a pool in custody). */
sig Peg {}
/** Slab — a contended resource under MOVEMENT semantics (a pool a movement is keyed on). */
sig Slab {}
/** Owner — the acting entity whose identity the intent records name. */
sig Owner extends Scoped {}
fact OwnerRefs { all o: Owner | no o.dataRefs }
/** Version — an opaque owner version (`owner_rid` / `toVersion`); PeerRid — an opaque peer row;
    Act — an opaque act name. Pure-presence atoms, pinned small in every command (gotcha 7). */
sig Version {}
sig PeerRid {}
sig Act {}

/** CiterOcc — a stand-in for a PEER module's committed row (DT-029 E2): an Action outside both chains'
    logs, bound to a key, citing an intent through the kernel's `arche`. Only the `unit_il_cit*` rows use it. */
sig CiterOcc extends Action { onKey: one Peg + Slab } { bindings = onKey }

fact HoldSpine { hold/spineAdopted }
fact MoveSpine { move/spineAdopted }

// Bindings: holders are Owners; the opaque fields range over the local atoms.
fact HoldBindings {
  all o: hold/HolderOcc   | o.holder in Owner.eId
  all o: hold/TransferOcc | o.from in Owner.eId and o.to in Owner.eId and o.toVersion in Version
  all o: hold/ReserveOcc  | o.ownerVersion in Version
  all o: hold/CitingOcc   | o.peerRid in PeerRid
  all o: hold/ActReserveOcc | o.act in Act
  all r: hold/IntentRec   | r.iVersion in Version and r.iAct in Act
}
fact MoveBindings {
  all o: move/HolderOcc   | o.holder in Owner.eId
  all o: move/TransferOcc | o.from in Owner.eId and o.to in Owner.eId and o.toVersion in Version
  all o: move/ReserveOcc  | o.ownerVersion in Version
  all o: move/CitingOcc   | o.peerRid in PeerRid
  all o: move/ActReserveOcc | o.act in Act
  all r: move/IntentRec   | r.iVersion in Version and r.iAct in Act
}

// ── witnesses (run; SAT = the scenario exists) ──────────────────────────────────────────────────
/** The happy path on a HOLD chain: RESERVE → CONFIRM(moved-by-this) → the key is HELD by the owner. */
run unit_il_reserveConfirmHolds {
  some k: Peg, r: hold/ReserveOcc, c: hold/ConfirmOcc | {
    r.subject = k and c.subject = k and precedes[r.tick, c.tick]
    committed[r] and committed[c] and c.holder = r.holder
    hold/phaseAt[k, c.tick] = I_HELD and hold/holderAt[k, c.tick] = r.holder
  }
} for 5 but 4 Int, 2 Peg, 1 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 1

/** Two owners race for one key: the second RESERVE is refused RKeyTaken before any peer act. */
run unit_il_raceLoserRefused {
  some k: Peg, disj a, b: hold/ReserveOcc | {
    a.subject = k and b.subject = k and precedes[a.tick, b.tick] and a.holder != b.holder
    committed[a] and refusedAtAdmission[b] and b.admission.because = RKeyTaken
  }
} for 5 but 4 Int, 2 Peg, 1 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 1

/** RELEASE on the peer's typed refusal (view unmoved): the key returns to FREE and a later
    RESERVE by another owner is admitted. */
run unit_il_releaseThenReserve {
  some k: Peg, r: hold/ReserveOcc, l: hold/ReleaseOcc, r2: hold/ReserveOcc | {
    r.subject = k and l.subject = k and r2.subject = k
    precedes[r.tick, l.tick] and precedes[l.tick, r2.tick]
    committed[r] and committed[l] and committed[r2]
    l.peerView = PV_UNMOVED and r2.holder != r.holder
    hold/phaseAt[k, l.tick] = I_FREE
  }
} for 5 but 4 Int, 2 Peg, 1 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 1

/** Rule R1 refusal: a RELEASE while the peer reads moved-by-this is refused RLanded. */
run unit_il_releaseLandedRefused {
  some k: Peg, r: hold/ReserveOcc, l: hold/ReleaseOcc | {
    r.subject = k and l.subject = k and precedes[r.tick, l.tick]
    committed[r] and l.holder = r.holder and l.peerView = PV_MOVED_BY_THIS
    refusedAtAdmission[l] and l.admission.because = RLanded
  }
} for 5 but 4 Int, 2 Peg, 1 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 1

/** Hand-over: HELD by o1 → TRANSFER(o1 → o2) → HELD by o2, one occurrence. */
run unit_il_transferHandsOver {
  some k: Peg, r: hold/ReserveOcc, c: hold/ConfirmOcc, x: hold/TransferOcc | {
    r.subject = k and c.subject = k and x.subject = k
    precedes[r.tick, c.tick] and precedes[c.tick, x.tick]
    committed[r] and committed[c] and committed[x]
    x.from = r.holder and x.to != r.holder
    hold/holderAt[k, x.tick] = x.to and hold/phaseAt[k, x.tick] = I_HELD
  }
} for 5 but 4 Int, 2 Peg, 1 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 1

/** Sub-intent round trip (KEEP mode): HELD → ACT_RESERVE(act) → ACT_CONFIRM → HELD again, same holder. */
run unit_il_subIntentRoundTrip {
  some k: Peg, c: hold/ConfirmOcc, a: hold/ActReserveOcc, b: hold/ActConfirmOcc | {
    c.subject = k and a.subject = k and b.subject = k
    precedes[c.tick, a.tick] and precedes[a.tick, b.tick]
    committed[c] and committed[a] and committed[b] and a.mode = AM_KEEP
    hold/phaseAt[k, a.tick] = I_ACTING and hold/pendingActAt[k, a.tick] = a.act
    hold/phaseAt[k, b.tick] = I_HELD and hold/holderAt[k, b.tick] = c.holder
  }
} for 5 but 4 Int, 2 Peg, 2 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 1   // at the CHECK scope: the checks over sub-intents are not vacuous (MINESWEEPER D2 review, point 6)

/** Closing sub-intent (the shelve leg): HELD → ACT_RESERVE(act, CLOSE) → ACT_CONFIRM frees the key in
    that same occurrence — no tick in which the key reads HELD with the peer gone back. */
run unit_il_closingSubIntentFrees {
  some k: Peg, c: hold/ConfirmOcc, a: hold/ActReserveOcc, b: hold/ActConfirmOcc | {
    c.subject = k and a.subject = k and b.subject = k
    precedes[c.tick, a.tick] and precedes[a.tick, b.tick]
    committed[c] and committed[a] and committed[b] and a.mode = AM_CLOSE
    hold/phaseAt[k, a.tick] = I_ACTING
    hold/phaseAt[k, b.tick] = I_FREE and no hold/holderAt[k, b.tick]
  }
} for 5 but 4 Int, 2 Peg, 2 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 1   // at the CHECK scope (point 6)

/** Invariant (b) refusal: a second ACT_RESERVE while one sub-intent is pending is refused RActPending. */
run unit_il_secondSubIntentRefused {
  some k: Peg, a, b: hold/ActReserveOcc | {
    a.subject = k and b.subject = k and precedes[a.tick, b.tick]
    committed[a] and refusedAtAdmission[b] and b.admission.because = RActPending
  }
} for 5 but 4 Int, 2 Peg, 2 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 1   // at the CHECK scope (point 6)

/** MOVEMENT: RESERVE → CONFIRM frees the key (I_DONE) and a second movement's RESERVE is admitted. */
run unit_il_movementFreesThenReserves {
  some k: Slab, r: move/ReserveOcc, c: move/ConfirmOcc, r2: move/ReserveOcc | {
    r.subject = k and c.subject = k and r2.subject = k
    precedes[r.tick, c.tick] and precedes[c.tick, r2.tick]
    committed[r] and committed[c] and committed[r2]
    move/phaseAt[k, c.tick] = I_DONE and no move/holderAt[k, c.tick]
  }
} for 5 but 4 Int, 1 Peg, 2 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 1

/** MOVEMENT refuses TRANSFER and sub-intents: RNotHoldSemantics. */
run unit_il_movementRefusesTransfer {
  some x: move/TransferOcc, a: move/ActReserveOcc |
    refusedAtAdmission[x] and RNotHoldSemantics in x.admission.because
    and refusedAtAdmission[a] and RNotHoldSemantics in a.admission.because
} for 5 but 4 Int, 1 Peg, 2 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 1

/** The lost-ack re-drive verdict: RESERVED × moved-by-this prescribes CONFIRM; the genesis cell
    prescribes the genesis; the HOLD's foreign-move cell prescribes release + detach. */
run unit_il_redriveCells {
  hold/redrive[I_RESERVED, PV_MOVED_BY_THIS] = RD_CONFIRM
  hold/redrive[I_RESERVED, PV_ABSENT] = RD_GENESIS
  move/redrive[I_RESERVED, PV_ABSENT] = RD_NOT_DEFINABLE
  hold/redrive[I_HELD, PV_MOVED_OTHERWISE] = RD_RELEASE_DETACH
  hold/redrive[I_FREE, PV_MOVED_BY_THIS] = RD_NOT_DEFINABLE
  move/redrive[I_FREE, PV_MOVED_BY_THIS] = RD_LATE_ACT_ALERT
  move/redrive[I_DONE, PV_MOVED_BY_THIS] = RD_SETTLED
} for 3 but 4 Int, 1 Peg, 1 Slab, 1 Owner, 1 Version, 1 PeerRid, 1 Act expect 1

// ── theorems (check; UNSAT = holds) ─────────────────────────────────────────────────────────────
assert unit_il_reserveReadsFree      { hold/reserveReadsFree and move/reserveReadsFree }
assert unit_il_reservationsSeparated { hold/reservationsSeparatedByFreeing and move/reservationsSeparatedByFreeing }
assert unit_il_oneLiveHolderPerKey   { hold/oneLiveHolderPerKey and move/oneLiveHolderPerKey }
assert unit_il_confirmRequiresLanded { hold/confirmRequiresLanded and move/confirmRequiresLanded }
assert unit_il_releaseRequiresUnlanded { hold/releaseRequiresUnlanded and move/releaseRequiresUnlanded }
assert unit_il_holdPersists          { hold/holdPersistsUntilRelease }
assert unit_il_movementFreesKey      { move/movementFreesKey }
assert unit_il_transferAtomic        { hold/transferAtomic }
assert unit_il_subIntentReturnsToHold { hold/subIntentReturnsToHold }
assert unit_il_oneSubIntentPerKey    { hold/oneSubIntentPerKey }
assert unit_il_subIntentsRequireHold { move/subIntentsRequireHold }
assert unit_il_redriveTotal          { hold/redriveTotal and move/redriveTotal }
assert unit_il_redriveIdempotent     { hold/redriveIdempotent and move/redriveIdempotent }
assert unit_il_guarantees            { hold/guarantees and move/guarantees }

check unit_il_reserveReadsFree       for 5 but 4 Int, 2 Peg, 2 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 0
check unit_il_reservationsSeparated  for 5 but 4 Int, 2 Peg, 2 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 0
check unit_il_oneLiveHolderPerKey    for 5 but 4 Int, 2 Peg, 2 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 0
check unit_il_confirmRequiresLanded  for 5 but 4 Int, 2 Peg, 2 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 0
check unit_il_releaseRequiresUnlanded for 5 but 4 Int, 2 Peg, 2 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 0
check unit_il_holdPersists           for 5 but 4 Int, 2 Peg, 2 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 0
check unit_il_movementFreesKey       for 5 but 4 Int, 2 Peg, 2 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 0
check unit_il_transferAtomic         for 5 but 4 Int, 2 Peg, 2 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 0
check unit_il_subIntentReturnsToHold for 5 but 4 Int, 2 Peg, 2 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 0
check unit_il_oneSubIntentPerKey     for 5 but 4 Int, 2 Peg, 2 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 0
check unit_il_subIntentsRequireHold  for 5 but 4 Int, 2 Peg, 2 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 0
check unit_il_redriveTotal           for 3 but 4 Int, 1 Peg, 1 Slab, 1 Owner, 1 Version, 1 PeerRid, 1 Act expect 0
check unit_il_redriveIdempotent      for 5 but 4 Int, 2 Peg, 2 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 0
check unit_il_guarantees             for 5 but 4 Int, 2 Peg, 2 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 0

// ── citation-derived attribution (DT-029 E2) — under `hold/citationView` ────────────────────────
/** A CONFIRM is admitted exactly when a committed peer row cites its RESERVE. */
run unit_il_citConfirmAdmitted {
  hold/citationView
  some k: Peg, r: hold/ReserveOcc, x: CiterOcc, c: hold/ConfirmOcc | {
    r.subject = k and c.subject = k and x.onKey = k and x.arche = r
    precedes[r.tick, x.tick] and precedes[x.tick, c.tick]
    committed[r] and committed[x] and committed[c] and c.holder = r.holder
  }
} for 5 but 4 Int, 2 Peg, 1 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 1

/** An UNCITED CONFIRM is refused RNotLanded — no peer row credits the intent. */
run unit_il_citUncitedConfirmRefused {
  hold/citationView
  some k: Peg, r: hold/ReserveOcc, c: hold/ConfirmOcc | {
    r.subject = k and c.subject = k and precedes[r.tick, c.tick] and committed[r] and c.holder = r.holder
    no x: CiterOcc | committed[x] and x.arche = r
    refusedAtAdmission[c] and c.admission.because = RNotLanded
  }
} for 5 but 4 Int, 2 Peg, 1 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 1

/** An OWN-LOG citer does not count: the chain's CONFIRM citing its own RESERVE never reads as the peer act
    (negative run — E1's finding made a rule). */
run unit_il_citOwnLogCiterDoesNotCount {
  hold/citationView
  some k: Peg, r: hold/ReserveOcc, c: hold/ConfirmOcc | {
    r.subject = k and c.subject = k and precedes[r.tick, c.tick] and committed[r] and c.arche = r
    hold/settledIntent[c] = r   // pin the intent c settles (the first run's witness slipped a RELEASE + a second RESERVE in between)
    no x: CiterOcc | committed[x] and x.arche = r
    committed[c]
  }
} for 5 but 4 Int, 2 Peg, 1 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 0

/** A SIBLING CHAIN's row does not count either: a MOVE-chain RESERVE citing the HOLD RESERVE (a nested intent) is an
    intent row, not the peer act — the CONFIRM stays refused (negative run; the E2 self-check's counterexample made a rule). */
run unit_il_citSiblingChainCiterDoesNotCount {
  hold/citationView
  some k: Peg, s: Slab, r: hold/ReserveOcc, m: move/ReserveOcc, c: hold/ConfirmOcc | {
    r.subject = k and m.subject = s and c.subject = k and m.arche = r and hold/settledIntent[c] = r
    precedes[r.tick, m.tick] and precedes[m.tick, c.tick] and committed[r] and committed[m] and c.holder = r.holder
    no x: CiterOcc | committed[x] and x.arche = r
    committed[c]
  }
} for 5 but 4 Int, 2 Peg, 1 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act expect 0

/** The ACT level: a citer of the pending ACT_RESERVE reads the act as landed — ACT_CONFIRM admitted, the hold
    continues (KEEP). */
run unit_il_citActCitationLands {
  hold/citationView
  some k: Peg, r: hold/ReserveOcc, x1: CiterOcc, c: hold/ConfirmOcc, a: hold/ActReserveOcc, x2: CiterOcc, b: hold/ActConfirmOcc | {
    r.subject = k and c.subject = k and a.subject = k and b.subject = k and x1.onKey = k and x2.onKey = k
    x1.arche = r and x2.arche = a and a.mode = AM_KEEP
    c.holder = r.holder and a.holder = r.holder and b.holder = r.holder
    precedes[r.tick, x1.tick] and precedes[x1.tick, c.tick] and precedes[c.tick, a.tick]
    precedes[a.tick, x2.tick] and precedes[x2.tick, b.tick]
    committed[r] and committed[x1] and committed[c] and committed[a] and committed[x2] and committed[b]
    hold/phaseAt[k, b.tick] = I_HELD
  }
} for 7 but 4 Int, 2 Peg, 1 Slab, 2 Owner, 2 Version, 2 PeerRid, 2 Act, 8 Tick, 7 Occurrence, 9 Snapshot expect 1
