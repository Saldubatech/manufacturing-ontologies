module meta/measurement/quantity

/*
 * V = Quantity instantiation of meta/measurement — the value-dependent statistics that need the
 * keyed value algebra (`meta/algebra/*`). LAST/FIRST/COUNT come from the generic module unchanged.
 *   MIN / MAX — over the period's values, via the keyed PARTIAL order (lone; present only when the
 *               values are pairwise comparable — typically a single-unit signal). Documented caveat.
 *   SUM       — the keyed Σ of a period's values. DEFERRED: it needs a keyed fold along the time
 *               order (the `meta/algebra` Σ-along-an-order helper that DT-007's by-Item Σ also wants);
 *               the spike meta/examples/ex14 shows the pattern with native Int `sum`. MEAN deferred
 *               (needs division, absent from the keyed monoid).
 *
 * NB the CROSS-SECTIONAL Σ (the by-Item total / CardCycle consolidation) is event-sourced UPSTREAM
 * (DT-006): a LEVEL signal's value is the running total of signed deltas, emitted as the measurement
 * value (ex14) and read back by LAST — so the framework needs no special sum for the inventory LEVEL
 * report. This module is the framework-side value-statistics; SUM here is the FLOW-signal temporal total.
 */

open meta/values                              // Quantity
open meta/algebra/keyed_order                 // lte (componentwise partial order), classify; → keyed_monoid add/zero
open meta/measurement/measurement[Quantity]   // Signal, Measurement, measurementsIn, latestIn/firstIn, lastValueIn, …

// ── MIN / MAX over a period's values (keyed PARTIAL order — lone; exists iff pairwise comparable) ──
/** MIN — the period value ≤ all others (componentwise). None if the values are incomparable. */
fun minIn[s: Signal, p: TimeInterval]: lone Quantity {
  { v: measurementsIn[s, p].value | all w: measurementsIn[s, p].value | lte[v.byUnit, w.byUnit] }
}
/** MAX — the period value ≥ all others (componentwise). None if incomparable. */
fun maxIn[s: Signal, p: TimeInterval]: lone Quantity {
  { v: measurementsIn[s, p].value | all w: measurementsIn[s, p].value | lte[w.byUnit, v.byUnit] }
}

/** metricResult — a Metric's value for a Quantity signal: LAST/FIRST/MIN/MAX. (COUNT is an Int — use
    the generic `countIn`; SUM needs the deferred keyed Σ-along-order; MEAN is deferred.) */
fun metricResult[m: Metric]: lone Quantity {
  m.stat = LAST  => lastValueIn[m.observes, m.over]
  else m.stat = FIRST => firstValueIn[m.observes, m.over]
  else m.stat = MIN  => minIn[m.observes, m.over]
  else m.stat = MAX  => maxIn[m.observes, m.over]
  else none
}
