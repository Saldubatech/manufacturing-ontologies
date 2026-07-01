module meta/model_time/model_time

/*
 * MODEL TIME — the ordinal / causal axis the model reasons about for PRECEDENCE and reachability
 * (DT-001.03 two-clock refinement). A `Tick` is an opaque logical position; ticks are TOTALLY ORDERED.
 *
 * Deliberately NOT domain time: a `Tick` carries no magnitude, no duration, no wall-clock — only
 * succession. Domain time (`Instant`/`Duration`, `meta/time`) is the valued, chronological axis; the two
 * meet only on `meta/occurrence`'s `Occurrence` bridge, never here.
 *
 * VOCABULARY (hard rule — modeling-conventions §3.3): causal words ONLY — `precedes` / `follows` /
 * `notAfter`. Never "earlier/before" (those are chronological, reserved for `Instant`; and `before` is a
 * reserved Alloy 6 temporal operator).
 *
 * Realized via `util/ordering[Tick]` — a genuine REIFIED total order (addressable, stampable atoms), NOT
 * the Alloy 6 `var`/trace: the occurrence log must be a queryable set of atoms a domain stamp can hang on
 * and a fold can range over (`keyed_sum[Occurrence]`). See DT-001.03 / DT-006.
 */

open util/ordering[Tick]

/** Tick — an opaque position in the model's causal total order (a logical-time point). */
sig Tick {}

/** precedes — `a` is strictly before `b` in the causal order (a < b). */
pred precedes[a, b: Tick] { lt[a, b] }

/** follows — `a` is strictly after `b` in the causal order (a > b). */
pred follows[a, b: Tick] { gt[a, b] }

/** notAfter — `a` precedes or equals `b` (a ≤ b). */
pred notAfter[a, b: Tick] { lte[a, b] }
