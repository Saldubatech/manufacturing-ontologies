module meta/time/time

/*
 * Abstract time — an `Instant` with an intrinsic total order, plus a closed `TimeInterval`.
 * This is a minimal, VALUE-layer seed of the deferred bitemporal clock (DT-001.03): just enough
 * to time-stamp measurements and bound calculation/reporting periods (see meta/measurement),
 * independent of the Alloy 6 `var`/trace machinery.
 *
 * The order is a global FACT (not a premise like `meta/keyed_value_algebra/keyed_order`'s `orderAxioms`): a
 * finite total order is ALWAYS satisfiable — unlike a ring-compatible order on `Scalar`, which
 * keyed_order must posit as a premise — and anyone who `open`s meta/time wants time ordered, so
 * the cost is localized to time-users by the module boundary.
 *
 * When DT-001.03 lands, `Instant` re-bases onto the real (bi)temporal clock; the order + interval
 * API here is the contract that survives.
 */

open meta/time/instant                           // the bare axis: Instant + order + TimeInterval (split 2026-07-02)
open meta/time/duration                          // Duration, ZeroDuration, dAtOrBefore — for the elapsed-time metric

// `Instant`, its total order + comparison vocabulary (atOrBefore, earlierThan, earliest/latest) and
// `TimeInterval`/`within` now live in meta/time/instant — split out so AXIS-ONLY consumers
// (meta/occurrence, and through it the whole action/log cone) do not carry the ARITY-4 metric below:
// Kodkod cannot represent an arity-4 relation once the universe exceeds ~215 atoms (2^31 tuple
// indices), and domain occurrence-log universes routinely do. This module keeps the elapsed-time
// METRIC only (the calendar moved to shared/time/calendar), re-exporting the axis to its openers.

// ── ABSTRACT period machinery (generic — how a timeline divides; NO real-world vocabulary) ──────
// The real-world CALENDARING binding (PeriodUnit HOUR/DAY/WEEK, TimeZone, CalendarSpec) lives in
// `shared/time/calendar` (2026-07-02 — the DT-001.12 earmark): units and zones are SHARED
// vocabulary; the division machinery below is essential domain-time modeling and stays in meta.

/** PeriodSpec — an ABSTRACT division of the timeline into periods: `closes` maps each instant to
    the close of its period. Partial here; made total + lawful by the `calendarAxioms` PREMISE. The
    real-world binding (which unit, which zone) is `shared/time/calendar`'s `CalendarSpec`. */
sig PeriodSpec { closes: Instant -> lone Instant }

/** endOfPeriod — the close of the period containing `t` under spec `ps` (lone; total under calendarAxioms). */
fun endOfPeriod[ps: PeriodSpec, t: Instant]: lone Instant { ps.closes[t] }
/** samePeriod — `a` and `b` share a period under `ps` (same close): an equivalence; with
    monotonicity, periods are contiguous. */
pred samePeriod[ps: PeriodSpec, a, b: Instant] { ps.closes[a] = ps.closes[b] }

/** calendarAxioms — the period-boundary laws, as a PREMISE (assume in period-reasoning commands;
    non-period models pay nothing). Enough to compute "level at end of period" with no arithmetic. */
pred calendarAxioms {
  all ps: PeriodSpec, t: Instant {
    one ps.closes[t]                                       // total: every instant has a close
    atOrBefore[t, ps.closes[t]]                            // the close is at/after t
    ps.closes[ps.closes[t]] = ps.closes[t]                 // idempotent (a close is its own close)
  }
  all ps: PeriodSpec, a, b: Instant |                      // monotone: later never closes earlier
    atOrBefore[a, b] implies atOrBefore[ps.closes[a], ps.closes[b]]
}

// ── Instant → Duration bridge: the elapsed-time metric (DT-010). `Duration` itself (the ordered value
//    type) lives in `meta/duration`, opened above; only the arity-4 metric over instants lives here. ──

/** the elapsed-time metric: `span[a][b]` = the Duration from `a` to `b`. */
one sig TimeMetric { span: Instant -> Instant -> lone Duration }
/** durationBetween — the elapsed Duration from `a` to `b` (present iff a ≤ b, under `durationAxioms`). */
fun durationBetween[a, b: Instant]: lone Duration { TimeMetric.span[a][b] }

/** durationAxioms — the elapsed-time laws, a PREMISE (assume it where staleness/elapsed reasoning is
    needed; other models pay nothing). Abstract: no arithmetic, just a monotone metric. */
pred durationAxioms {
  all a: Instant | durationBetween[a, a] = ZeroDuration                       // no time at a point
  all a, b: Instant | some durationBetween[a, b] iff atOrBefore[a, b]         // defined for a ≤ b
  all a, b, c: Instant |                                                       // monotone: extend the end ⇒ ≥
    (atOrBefore[a, b] and atOrBefore[b, c]) implies
      dAtOrBefore[durationBetween[a, b], durationBetween[a, c]]
}
