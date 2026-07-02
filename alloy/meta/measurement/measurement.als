module meta/measurement/measurement[V]

/*
 * Measurements & Metrics — the Signal → Measurement → Metric → Report chain, reified once and
 * reused. Generic over the measured VALUE type `V` (e.g. Quantity, a Scalar, a discrete State);
 * the value-agnostic structure + selectors live here, while value-dependent statistics
 * (MIN/MAX/SUM/MEAN) are added by an instantiating module (see measurement/quantity.als for V=Quantity).
 *
 * Vocabulary (after Pinilla, "Measurements and Metrics"):
 *   Signal       — an observable phenomenon (here, a value over time).
 *   Measurement  — assigning a value to a Signal at an Instant (EVENT-driven: one sample per change,
 *                  no fixed sampling clock — the sample history IS the operation/event log).
 *   Metric       — a statistic over the measurements in a Calculation Period.
 *   Report       — a Metric sampled across a Reporting Period at a Calculation-Period granularity,
 *                  recomputed every Metric Interval (absent = on-demand).
 *
 * Time comes from meta/time (abstract ordered Instant; DT-001.03 seed). Values are opaque here;
 * `shared/measurement/quantity` binds V = Quantity and supplies the keyed statistics.
 */

open meta/time/time            // Instant, TimeInterval, PeriodUnit, TimeZone, endOfPeriod, within, …
                          // NB: deliberately does NOT open shared/values, so Quantity stays single-path
                          // for the [Quantity] instantiation (avoids parameterized-open ambiguity);
                          // and so meta/time's cost stays confined to measurement-users.

/** SignalKind — how a signal reads BETWEEN samples / how it aggregates over time.
    LEVEL = step / last-observation-carried-forward (e.g. inventory on-hand) — temporal stat is
    typically LAST/MIN/MAX/MEAN, never SUM. FLOW = an amount per event (e.g. units consumed) —
    summable over time. DISCRETE = discrete events/states. */
enum SignalKind { LEVEL, FLOW, DISCRETE }

/** Signal — an observable phenomenon; its history is its `Measurement`s. */
sig Signal { kind: one SignalKind }

/** Measurement — one sample of a Signal at an Instant. Event-driven: at most one per
    `(of, at)` (a signal has a single value at any instant). */
sig Measurement { of: one Signal, at: one Instant, value: one V }
fact OneSamplePerInstant {
  all disj m1, m2: Measurement | (m1.of = m2.of and m1.at = m2.at) implies m1 = m2
}
// Tight by default: every sample belongs to a real signal (true by `of: one Signal`); no orphan
// signals required — a signal with no samples is a legitimate "not-yet-observed" signal.

/** Stat — the statistic a Metric computes over the measurements in its Calculation Period.
    LAST/FIRST/COUNT are value-agnostic (defined here); MIN/MAX/SUM/MEAN are value-dependent
    (defined per value type — see quantity.als; MEAN is deferred, it needs division). */
enum Stat { LAST, FIRST, MIN, MAX, COUNT, SUM, MEAN }

/** Metric — apply `stat` to the measurements of `observes` within `over` (the Calculation Period). */
sig Metric { observes: one Signal, stat: one Stat, over: one TimeInterval }

/** Report — a (stat, signal) sampled across `window` (the Reporting Period), one value per
    `granularity` Calculation Period (a PeriodUnit: HOUR/DAY/WEEK), in time zone `zone`, recomputed
    every `cadence` (Metric Interval; none = on-demand). The per-period series is produced downstream
    from `window`/`granularity`/`zone` (each period's close via `endOfPeriod`). */
sig Report {
  observes:    one Signal,
  stat:        one Stat,
  window:      one TimeInterval,
  granularity: one PeriodUnit,
  zone:        one TimeZone,
  cadence:     lone PeriodUnit
}

// ── selectors (VALUE-AGNOSTIC — available for any V) ─────────────────────────────────────────
/** measurementsIn — the samples of `s` whose instant falls in `p`. */
fun measurementsIn[s: Signal, p: TimeInterval]: set Measurement {
  { m: Measurement | m.of = s and within[m.at, p] }
}

/** latestIn — the last (latest-instant) sample of `s` in `p` (lone). */
fun latestIn[s: Signal, p: TimeInterval]: lone Measurement {
  { m: measurementsIn[s, p] | m.at = latest[measurementsIn[s, p].at] }
}
/** firstIn — the first sample of `s` in `p` (lone). */
fun firstIn[s: Signal, p: TimeInterval]: lone Measurement {
  { m: measurementsIn[s, p] | m.at = earliest[measurementsIn[s, p].at] }
}

/** LAST — the value of the period's last sample (the prescribed "level at end of period"). */
fun lastValueIn[s: Signal, p: TimeInterval]: lone V { latestIn[s, p].value }
/** FIRST — the value of the period's first sample. */
fun firstValueIn[s: Signal, p: TimeInterval]: lone V { firstIn[s, p].value }
/** COUNT — number of samples in the period. */
fun countIn[s: Signal, p: TimeInterval]: Int { #measurementsIn[s, p] }

/** latestAtOrBefore — the last sample of `s` at-or-before instant `t` (lone). */
fun latestAtOrBefore[s: Signal, t: Instant]: lone Measurement {
  { m: Measurement | m.of = s and atOrBefore[m.at, t] and
      m.at = latest[{ x: Measurement | x.of = s and atOrBefore[x.at, t] }.at] }
}
/** valueAt — LOCF read of a (LEVEL) signal: the value carried at instant `t` = the value of the
    last sample at-or-before `t`. Undefined (none) before the signal's first sample. */
fun valueAt[s: Signal, t: Instant]: lone V { latestAtOrBefore[s, t].value }
