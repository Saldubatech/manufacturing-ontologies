module meta/certainty/certainty

/*
 * Certainty (confidence) levels and staleness decay (DT-010). An inventory count/level has a confidence
 * SUPPLIED by the operation that last touched it, which DECAYS toward lower certainty as time passes —
 * step-wise through a finite, ordered set of levels, with monotonically increasing time thresholds.
 *
 * This module models the modelable core: the ORDERED level set + the rule that decay NEVER RAISES
 * certainty (the computed level is at-or-below the operation-supplied start). It is a COMPUTED value, not
 * stored.
 *
 * PENDING (needs machinery not yet built): mapping elapsed time → number of steps requires a time-metric
 * (Duration arithmetic on the effective axis `meta/time`, currently an opaque order with no subtraction),
 * and reading the start level + last-operation time off the item requires the reified Operation /
 * effective-time layer (DT-006 / DT-001.03). See design-topics/dt-010-confidence-and-staleness.md.
 */

/** CertaintyLevel — the ordered confidence levels of a count (LOW < MEDIUM < HIGH). */
abstract sig CertaintyLevel {}
one sig LOW    extends CertaintyLevel {}
one sig MEDIUM extends CertaintyLevel {}
one sig HIGH   extends CertaintyLevel {}

/** lteC — the certainty order, reflexive: LOW ≤ MEDIUM ≤ HIGH. (Explicit relation — deterministic, no
    dependence on `util/ordering`'s atom ordering.) */
pred lteC[a, b: CertaintyLevel] {
  a -> b in (LOW->LOW + LOW->MEDIUM + LOW->HIGH + MEDIUM->MEDIUM + MEDIUM->HIGH + HIGH->HIGH)
}

/** atOrBelow — the levels no MORE certain than `l` (`l` and everything lower) — the set reachable under
    staleness decay starting from `l`. */
fun atOrBelow[l: CertaintyLevel]: set CertaintyLevel { { x: CertaintyLevel | lteC[x, l] } }

/** computedFrom — a staleness-decayed level `computed` relative to the operation-supplied `start`: decay
    NEVER raises certainty, so `computed` is at-or-below `start`. The actual level is `start` stepped down
    once per crossed time threshold (a finite, monotone schedule); that elapsed-time → step mapping is
    pending a time-metric (see the module header / DT-010). */
pred computedFrom[computed, start: CertaintyLevel] { computed in atOrBelow[start] }
