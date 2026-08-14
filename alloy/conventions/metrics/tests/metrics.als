module conventions/metrics/tests/metrics

open conventions/metrics/metrics

/*
 * Root for the METRICS exemplar (DT-007/DT-008 read side). The light conventions cone
 * affords the REAL keyed_sum fold the core metrics cone cannot (arity-4 budget) — this root
 * doubles as the fold-pinning recipe in action.
 */

// ── the DT-008 bridge holds: over one meter, the cell IS the state read ─────────────────────────
assert conv_mx_bridge { cellBridgesToState }
check conv_mx_bridge for 6 but 5 Int, 3 Scalar, 1 Meter, 8 Tick, 5 EntityId, 6 Snapshot, 4 Quantity expect 0

// ── non-vacuity: a one-meter cell with real content ─────────────────────────────────────────────
run conv_mx_oneMeterCell {
  some m: Meter, s: SetOcc | {
    committed[s] and s.subject = m
    notAfter[s.tick, Sample.at]
    some cell
    cell = meterValAt[m, Sample.at]
  }
} for 6 but 5 Int, 3 Scalar, 1 Meter, 8 Tick, 5 EntityId, 6 Snapshot, 4 Quantity expect 1

// ── the Σ with real content: TWO meters, the cell adds their as-of values ───────────────────────
run conv_mx_twoMeterSum {
  some disj m1, m2: Meter | {
    some meterValAt[m1, Sample.at] and some meterValAt[m2, Sample.at]
    cell = add[meterValAt[m1, Sample.at], meterValAt[m2, Sample.at]]
    some cell
  }
} for 6 but 5 Int, 3 Scalar, 2 Meter, 9 Tick, 6 EntityId, 8 Snapshot, 6 Quantity expect 1

// ── SAMPLING IS AS-OF: a reading set AFTER the instant does not move the cell ───────────────────
run conv_mx_samplingIsAsOf {
  some m: Meter, s1, s2: SetOcc | {
    committed[s1] and committed[s2]
    s1.subject = m and s2.subject = m
    notAfter[s1.tick, Sample.at] and precedes[Sample.at, s2.tick]
    s1.qty != s2.qty
    cell = qtyMap[s1.qty]        // the cell reads the AS-OF value…
    cell != qtyMap[s2.qty]        // …not the later one
  }
} for 6 but 5 Int, 3 Scalar, 1 Meter, 9 Tick, 5 EntityId, 7 Snapshot, 5 Quantity expect 1

// ── LOCF at the read: an installed meter with no reading contributes the keyed zero ─────────────
run conv_mx_unreadMeterContributesZero {
  some m: Meter | {
    meterStartedAt[m, Sample.at]
    no meterValAt[m, Sample.at]
    no s: SetOcc | committed[s]
    no cell
  }
} for 5 but 5 Int, 3 Scalar, 1 Meter, 6 Tick, 4 EntityId, 4 Snapshot, 2 Quantity expect 1
