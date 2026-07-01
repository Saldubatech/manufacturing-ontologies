module meta/occurrence/occurrence

/*
 * The BRIDGE between the two clocks (DT-001.03). An `Occurrence` is something that happens: it has a
 * position in MODEL TIME (`tick`) and a stamp in DOMAIN TIME (`at: Instant`).
 *
 * This is the ONLY module that names both clocks. Keeping the tie here means neither pure clock module
 * (`meta/time`, `meta/model_time`) references the other, so the two can never be conflated. DT-006's
 * operation occurrences `extend Occurrence`; the op-log fold is `keyed_sum[Occurrence]` ordered by `tick`,
 * with `at` used only for chronological reads (period bucketing, staleness).
 */

open meta/model_time/model_time   // Tick, precedes, follows, notAfter
open meta/time/time               // Instant, atOrBefore, earlierThan

/** Occurrence — something that happens: a model-time position + a domain-time (effective) stamp. */
abstract sig Occurrence {
  tick: one Tick,        // model time  — WHERE in the causal order
  at:   one Instant      // domain time — the effective real-world stamp
}

/** Ticks linearize occurrences — at most one occurrence per tick — so the causal order is a strict
    total order on occurrences (not merely on the underlying ticks). */
fact OneOccurrencePerTick { all disj a, b: Occurrence | a.tick != b.tick }

/** occPrecedes — the causal (model-time) order lifted to occurrences. */
pred occPrecedes[a, b: Occurrence] { precedes[a.tick, b.tick] }

/** clocksAligned — the consistency PREMISE between the two clocks (NOT a global fact): the domain stamp
    is monotone along the causal order. Forward-monotone by default; NOT assuming it admits BACKDATING
    (an occurrence late in model time, early in domain time) — the seam toward bitemporality. Assume it
    where forward-only reasoning is wanted (mirrors `calendarAxioms` / `durationAxioms`). */
pred clocksAligned { all disj a, b: Occurrence | occPrecedes[a, b] implies atOrBefore[a.at, b.at] }
