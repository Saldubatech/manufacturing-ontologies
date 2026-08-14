module meta/profiles/timed_log

/*
 * P2 — TIMED LOG: the domain-log profile + wall-clock time (DT-012). For modules answering
 * WHEN-questions: as-of-date reads, period reports, staleness, backdating. Brings the `Timed`
 * subset extension (opt KINDS in per fact: `MyOcc in Timed`) and the bare Instant axis.
 *
 * Deliberately NOT bundled as facts: `clocksAligned` (assuming it forbids backdating — assume it
 * per root where forward-only chronology is wanted), and `calendarAxioms`/`durationAxioms`
 * (period-close and elapsed-metric laws — add per root when the metric in question needs them).
 */

open meta/profiles/domain_log     // P1 (and transitively P0)
open meta/occurrence/timed        // Timed in Occurrence { at } + clocksAligned (a PREMISE, not a fact)

/** P_TimedLog — the marker: this universe models under the timed-log profile. */
one sig P_TimedLog extends Profile {}
