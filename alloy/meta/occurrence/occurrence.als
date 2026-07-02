module meta/occurrence/occurrence

/*
 * Occurrence — something that happens: an entry in the LOG, at a position in MODEL TIME (`tick`).
 *
 * MINIMAL BY DESIGN (DT-011, 2026-07-02): the core carries ONLY the causal position. The domain-time
 * stamp (`at: Instant`) is the OPT-IN subset extension `meta/occurrence/timed` — most log reasoning
 * (chaining, projections, guards) never needs wall-clock time, and carrying it by default put the
 * whole Instant family (and the two-clock bridge premise) into every log universe. Open `timed` where
 * chronological reads (period bucketing, staleness, as-of-wall-time) are actually wanted.
 */

open meta/model_time/model_time   // Tick, precedes, follows, notAfter

/** Occurrence — something that happens: a model-time (causal) position in the log. */
abstract sig Occurrence {
  tick: one Tick         // model time — WHERE in the causal order
}

/** Ticks linearize occurrences — at most one occurrence per tick — so the causal order is a strict
    total order on occurrences (not merely on the underlying ticks). */
fact OneOccurrencePerTick { all disj a, b: Occurrence | a.tick != b.tick }

/** occPrecedes — the causal (model-time) order lifted to occurrences. */
pred occPrecedes[a, b: Occurrence] { precedes[a.tick, b.tick] }
