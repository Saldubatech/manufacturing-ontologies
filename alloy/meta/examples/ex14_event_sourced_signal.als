module meta/examples/ex14_event_sourced_signal

/*
 * PATTERN:  Event-sourcing a LEVEL signal from a reified, time-stamped operation log — and reading
 *           it back through meta/measurement. The level at any instant is the running total of
 *           signed delta-events at-or-before it; the framework's LOCF read agrees. SPIKE for DT-006
 *           (operations as first-class entities) feeding DT-008 (measurements) — the G3 substrate.
 * UML:      an event/command log (append-only) + a derived state projection.
 * FP:       a fold (scan) of a delta stream ordered by time; level = prefix-sum.
 * USE WHEN:  you need history/as-of/period reports over a quantity that changes only at events
 *           (inventory on-hand, occupancy, balance) — the timestamped event IS the measurement.
 * AVOID:     trying to aggregate across an UNORDERED set at one instant (a cross-sectional fold with
 *           no order). Event-sourcing turns that into a sum along TIME (here, native Int `sum`).
 * SEE ALSO:  meta/time; meta/measurement; DT-006; DT-008 (dt-008-measurement-framework.md);
 *           the inventory analogue: on-hand = check-in/out → occupancy here.
 *
 * Neutral cast: a Hotel's OCCUPANCY (rooms occupied). Check-in = +1, check-out = −1. Occupancy is a
 * LEVEL signal; the StayEvent log is the reified, timestamped operation history.
 */

open meta/time/time                              // Instant, atOrBefore, earlierThan, PeriodSpec, endOfPeriod, calendarAxioms
open meta/measurement/measurement[Int]      // Signal, Measurement, valueAt (LOCF), … over Int-valued signals

// ── the one tracked signal: hotel occupancy (a LEVEL signal) ────────────────────────────────
one sig occupancy in Signal {}
fact OneLevelSignal { Signal = occupancy and occupancy.kind = LEVEL }

// ── the reified operation log: timestamped occupancy deltas (check-in +1 / check-out −1) ───────
sig StayEvent { at: one Instant, delta: one Int }
fact OneEventPerInstant { all disj a, b: StayEvent | a.at != b.at }
fact CheckInOrOut       { all e: StayEvent | e.delta = 1 or e.delta = -1 }

/** occupancyAt — the EVENT-SOURCED level: Σ of the deltas of all events at-or-before `t`. Native Int
    `sum` over the time-filtered log — no cross-sectional set-fold, no recurrence machinery. */
fun occupancyAt[t: Instant]: Int { sum e: { x: StayEvent | atOrBefore[x.at, t] } | e.delta }

// ── feed the framework: one Measurement per event, valued at the event-sourced level then ──────
fact EmitMeasurements {
  Measurement.of in occupancy                         // every sample is of the occupancy signal
  StayEvent.at = Measurement.at                       // samples sit exactly at the event instants
  all m: Measurement | m.value = occupancyAt[m.at]    // each sample's value = the level at its instant
}

/** endOfPeriodLevel — the occupancy at the close of `t`'s period under `ps` (the prescribed
    end-of-period metric), composing the framework's `endOfPeriod` with the event-sourced level. */
fun endOfPeriodLevel[ps: PeriodSpec, t: Instant]: Int { occupancyAt[endOfPeriod[ps, t]] }

// ── it works (expect SAT) ───────────────────────────────────────────────────────────────────
// A concrete trace: check-in, check-in, check-out → occupancy ends at 1.
run unit_ex14_occupancyTrace {
  some disj e1, e2, e3: StayEvent |
    earlierThan[e1.at, e2.at] and earlierThan[e2.at, e3.at]
    and e1.delta = 1 and e2.delta = 1 and e3.delta = -1
    and occupancyAt[e3.at] = 1
} for 6 expect 1

// An end-of-period (e.g. end-of-day) occupancy reading exists.
run unit_ex14_endOfPeriod {
  calendarAxioms and (some ps: PeriodSpec, t: Instant | some endOfPeriodLevel[ps, t])
} for 5 expect 1

// ── the pressure test (check; UNSAT = holds) ─────────────────────────────────────────────────
// THE CLAIM: meta/measurement's LOCF read over the emitted samples EQUALS the event-sourced
// cumulative, at every instant at/after the first event. If this holds, the op-log → Signal wiring
// is sound: the framework needs no special "sum"; the event log already carries the level.
assert unit_ex14_frameworkMatchesEventSource {
  all t: Instant | (some e: StayEvent | atOrBefore[e.at, t]) implies valueAt[occupancy, t] = occupancyAt[t]
}
check unit_ex14_frameworkMatchesEventSource for 6 expect 0

// The level is a STEP/LOCF signal: with no event in (s, t], occupancy is unchanged across [s, t].
assert unit_ex14_changesOnlyAtEvents {
  all s, t: Instant |
    (atOrBefore[s, t] and (no e: StayEvent | earlierThan[s, e.at] and atOrBefore[e.at, t]))
      implies occupancyAt[s] = occupancyAt[t]
}
check unit_ex14_changesOnlyAtEvents for 6 expect 0
