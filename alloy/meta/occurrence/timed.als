module meta/occurrence/timed

/*
 * Timed — the OPT-IN domain-time stamp on occurrences (DT-011 demotion, 2026-07-02): the two-clock
 * BRIDGE of DT-001.03, now an extension rather than the default anatomy. This is the ONLY module that
 * names both clocks (`Tick` via Occurrence, `Instant` here), so the two can never be conflated
 * (modeling-conventions §3.3).
 *
 * A SUBSET sig (not `extends`): opt-ins must compose — a kind may be any combination of {timed,
 * attributed, stateful}, and Alloy has single inheritance. A domain opts a KIND in with one fact
 * (e.g. `MeasurementOcc in Timed`); mixed models may leave other occurrences un-stamped.
 */

open meta/occurrence/occurrence   // Occurrence, occPrecedes
open meta/time/instant            // the bare Instant axis (atOrBefore) — NOT the arity-4 metric

/** Timed — an occurrence carrying its domain-time (effective) stamp. */
sig Timed in Occurrence { at: one Instant }

/** clocksAligned — the consistency PREMISE between the two clocks (NOT a global fact): the domain
    stamp is monotone along the causal order, over the timed occurrences. Forward-monotone by default;
    NOT assuming it admits BACKDATING (an occurrence late in model time, early in domain time) — the
    seam toward bitemporality. Assume it where forward-only reasoning is wanted (mirrors
    `calendarAxioms` / `durationAxioms`). */
pred clocksAligned { all disj a, b: Timed | occPrecedes[a, b] implies atOrBefore[a.at, b.at] }
