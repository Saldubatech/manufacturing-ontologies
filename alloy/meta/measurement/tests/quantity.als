module meta/measurement/tests/quantity

/*
 * Tests for the V=Quantity instantiation: MIN/MAX (keyed partial order) and the metricResult dispatch.
 * Under the keyed_order premise (ringAxioms + orderAxioms) so the algebra is meaningful, like the
 * inventory_item tests. (Temporal SUM is deferred — see quantity.als.)
 */

open meta/measurement/quantity

fact ScalarPremises { ringAxioms and orderAxioms }

// ── coherence (expect SAT) ────────────────────────────────────────────────────────────────
// A period with two comparable values: MIN and MAX both exist and are sampled values.
run unit_q_minMax {
  some s: Signal, p: TimeInterval |
    some minIn[s, p] and some maxIn[s, p]
    and minIn[s, p] in measurementsIn[s, p].value
    and maxIn[s, p] in measurementsIn[s, p].value
} for 5 but 3 Scalar

// A single-sample period: MIN = MAX = that value.
run unit_q_minMaxSingle {
  some s: Signal, p: TimeInterval, m: Measurement |
    measurementsIn[s, p] = m and minIn[s, p] = m.value and maxIn[s, p] = m.value
} for 5 but 3 Scalar

// metricResult dispatches LAST / MIN to the right selector.
run unit_q_dispatch {
  (some mt: Metric | mt.stat = LAST and metricResult[mt] = lastValueIn[mt.observes, mt.over])
  and (some mt: Metric | mt.stat = MIN and metricResult[mt] = minIn[mt.observes, mt.over])
} for 5 but 3 Scalar

// ── invariants (check; UNSAT = holds) ───────────────────────────────────────────────────────
// MIN ≤ MAX whenever both exist.
assert unit_q_minLeMax {
  all s: Signal, p: TimeInterval |
    (some minIn[s, p] and some maxIn[s, p]) implies lte[minIn[s, p].byUnit, maxIn[s, p].byUnit]
}
check unit_q_minLeMax for 5 but 3 Scalar

// MIN/MAX, when present, are actual sampled values of the period.
assert unit_q_minMaxSampled {
  all s: Signal, p: TimeInterval |
    (some minIn[s, p] implies minIn[s, p] in measurementsIn[s, p].value)
    and (some maxIn[s, p] implies maxIn[s, p] in measurementsIn[s, p].value)
}
check unit_q_minMaxSampled for 5 but 3 Scalar

// metricResult agrees with the generic LAST/FIRST selectors.
assert unit_q_dispatchLastFirst {
  all mt: Metric |
    (mt.stat = LAST implies metricResult[mt] = lastValueIn[mt.observes, mt.over])
    and (mt.stat = FIRST implies metricResult[mt] = firstValueIn[mt.observes, mt.over])
}
check unit_q_dispatchLastFirst for 5 but 3 Scalar
