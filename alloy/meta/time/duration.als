module meta/time/duration

/*
 * Duration — a length of elapsed time as an abstract, totally ordered VALUE type (opaque like `Instant`;
 * Alloy has no reals). Ordered so elapsed times compare to thresholds (the staleness metric, DT-010).
 *
 * Deliberately LIGHTWEIGHT and standalone: it carries only the value type + its order, NO instants and NO
 * arity-4 time-metric. Value-object users (e.g. `ItemSupply.averageLeadTime` via `shared/values`) open THIS
 * module so they do not drag the heavier `meta/time` machinery (`TimeMetric.span` is arity-4 and blows up
 * representation in large-scope roots such as kanban_card / system). The instant→duration bridge
 * (`TimeMetric.span`, `durationBetween`, `durationAxioms`) lives in `meta/time`, which opens this module.
 */

/** Duration — a length of elapsed time; `dlte` is the ≤ relation (`d.dlte` = the durations ≥ d). */
sig Duration { dlte: set Duration }
/** ZeroDuration — no elapsed time (the minimum duration). */
one sig ZeroDuration in Duration {}
fact DurationIsTotalOrder {
  all d: Duration | d in d.dlte                                      // reflexive
  all a, b: Duration | (b in a.dlte and a in b.dlte) implies a = b   // antisymmetric
  all a, b, c: Duration | (b in a.dlte and c in b.dlte) implies c in a.dlte   // transitive
  all a, b: Duration | b in a.dlte or a in b.dlte                    // total
  all d: Duration | d in ZeroDuration.dlte                           // zero is the minimum
}
/** dAtOrBefore — d1 ≤ d2 (d1 is no longer than d2). */
pred dAtOrBefore[d1, d2: Duration] { d2 in d1.dlte }
