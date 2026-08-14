module conventions/denormalized_observables/tests/denormalized_observables

open conventions/denormalized_observables/denormalized_observables

/*
 * Root for the DENORMALIZED-OBSERVABLES exemplar (domain-log-kit §denormalized-observables).
 * The keyed-Quantity vocabulary rides shared/values; scopes pin the quantity families small.
 */

// ── the incremental-effect law holds ────────────────────────────────────────────────────────────
assert conv_do_accrues { accrues }
check conv_do_accrues for 6 but 5 Int, 3 Scalar, 1 Tally, 9 Tick, 6 EntityId, 8 Snapshot, 6 Quantity expect 0

// ── the COMPLETENESS reading is a THEOREM (0/1/2 postings — the case-wise discharge) ────────────
assert conv_do_totalIsAccumulated { all t: Tally, k: Tick | totalIsAccumulated[t, k] }
check conv_do_totalIsAccumulated for 6 but 5 Int, 3 Scalar, 1 Tally, 2 AddOcc, 9 Tick, 6 EntityId, 8 Snapshot, 6 Quantity expect 0

// ── non-vacuity: the accumulating end exists ────────────────────────────────────────────────────
run conv_do_twoPostingsAccumulate {
  some disj p1, p2: AddOcc, t: Tally, k: Tick | {
    committed[p1] and committed[p2]
    p1.subject = t and p2.subject = t
    precedes[p1.tick, p2.tick] and notAfter[p2.tick, k]
    totalAt[t, k] = add[qtyMap[p1.qty], qtyMap[p2.qty]]
    some totalAt[t, k]
  }
} for 6 but 5 Int, 3 Scalar, 1 Tally, 9 Tick, 6 EntityId, 8 Snapshot, 6 Quantity expect 1

// ── the empty end: genesis reads the keyed zero ─────────────────────────────────────────────────
run conv_do_zeroBeforePostings {
  some t: Tally, k: Tick | {
    startedTallyAt[t, k]
    no p: AddOcc | committed[p]
    no totalAt[t, k]
  }
} for 5 but 5 Int, 3 Scalar, 1 Tally, 6 Tick, 5 EntityId, 5 Snapshot, 3 Quantity expect 1

// ── BEYOND the case-wise window the value is STILL LAW-DEFINED (pairwise induction): three
// postings accumulate correctly even though no fold and no 3-case exists anywhere ───────────────
run conv_do_threePostingsStillDefined {
  some disj p1, p2, p3: AddOcc, t: Tally, k: Tick | {
    committed[p1] and committed[p2] and committed[p3]
    p1.subject = t and p2.subject = t and p3.subject = t
    precedes[p1.tick, p2.tick] and precedes[p2.tick, p3.tick] and notAfter[p3.tick, k]
    totalAt[t, k] = add[add[qtyMap[p1.qty], qtyMap[p2.qty]], qtyMap[p3.qty]]
  }
} for 7 but 5 Int, 3 Scalar, 1 Tally, 10 Tick, 6 EntityId, 9 Snapshot, 8 Quantity expect 1
