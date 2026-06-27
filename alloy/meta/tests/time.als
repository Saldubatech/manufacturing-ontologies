module meta/tests/time

open meta/time

/*
 * Sanity suite for meta/time: the order is a genuine total order, earliest/latest pick the
 * endpoints, and interval membership behaves. SAT = a witnessing instance; UNSAT (check) = the
 * property holds in every instance.
 */

// ── coherence (expect SAT) ────────────────────────────────────────────────────────────────
// A non-trivial chain of three distinct, strictly-ordered instants exists.
run unit_time_chain {
  some disj a, b, c: Instant | earlierThan[a, b] and earlierThan[b, c]
} for 4

// An interval that strictly contains a third instant.
run unit_time_intervalContains {
  some i: TimeInterval, t: Instant | earlierThan[i.from, t] and earlierThan[t, i.to]
} for 4

// earliest/latest of a 3-element set are its min/max.
run unit_time_endpoints {
  some disj a, b, c: Instant |
    earlierThan[a, b] and earlierThan[b, c] and earliest[a+b+c] = a and latest[a+b+c] = c
} for 4

// ── invariants (check; UNSAT = holds) ───────────────────────────────────────────────────────
// The order is total: any two instants are comparable.
assert unit_time_total {
  all a, b: Instant | atOrBefore[a, b] or atOrBefore[b, a]
}
check unit_time_total for 6

// earliest/latest are unique when present (a consequence of antisymmetry + totality).
assert unit_time_endpointsUnique {
  all ts: set Instant | lone earliest[ts] and lone latest[ts]
}
check unit_time_endpointsUnique for 6

// A non-empty set always has both an earliest and a latest.
assert unit_time_nonEmptyHasEndpoints {
  all ts: set Instant | some ts implies (some earliest[ts] and some latest[ts])
}
check unit_time_nonEmptyHasEndpoints for 6

// within is exactly bounded by the endpoints.
assert unit_time_withinBounds {
  all t: Instant, i: TimeInterval |
    within[t, i] iff (atOrBefore[i.from, t] and atOrBefore[t, i.to])
}
check unit_time_withinBounds for 6

// ── period boundaries (PeriodSpec / endOfPeriod) — under the calendarAxioms premise ─────────────
// SAT: two distinct instants in the SAME period (a non-degenerate period).
run unit_time_samePeriod {
  calendarAxioms and (some ps: PeriodSpec, disj a, b: Instant | earlierThan[a, b] and samePeriod[ps, a, b])
} for 4

// SAT: two instants in DIFFERENT periods (boundaries actually divide the timeline).
run unit_time_differentPeriods {
  calendarAxioms and (some ps: PeriodSpec, disj a, b: Instant | not samePeriod[ps, a, b])
} for 4

// check: the close is always at-or-after the instant.
assert unit_time_closeAtOrAfter {
  calendarAxioms implies all ps: PeriodSpec, t: Instant | atOrBefore[t, endOfPeriod[ps, t]]
}
check unit_time_closeAtOrAfter for 4

// check: idempotent — the close of a close is itself.
assert unit_time_closeIdempotent {
  calendarAxioms implies all ps: PeriodSpec, t: Instant | endOfPeriod[ps, endOfPeriod[ps, t]] = endOfPeriod[ps, t]
}
check unit_time_closeIdempotent for 4

// check: samePeriod is an equivalence relation.
assert unit_time_samePeriodEquiv {
  calendarAxioms implies all ps: PeriodSpec, a, b, c: Instant |
    samePeriod[ps, a, a]
    and (samePeriod[ps, a, b] implies samePeriod[ps, b, a])
    and ((samePeriod[ps, a, b] and samePeriod[ps, b, c]) implies samePeriod[ps, a, c])
}
check unit_time_samePeriodEquiv for 4

// check: an instant shares its period with its own close (a consequence of idempotence).
assert unit_time_inOwnPeriod {
  calendarAxioms implies all ps: PeriodSpec, t: Instant | samePeriod[ps, t, endOfPeriod[ps, t]]
}
check unit_time_inOwnPeriod for 4
