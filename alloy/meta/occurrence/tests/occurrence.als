module meta/occurrence/tests/occurrence

open meta/occurrence/occurrence

/*
 * The MINIMAL core (DT-011): occurrences carry only their causal position. The domain-time stamp and
 * the two-clock bridge live in the `timed` extension (tests/timed.als). `Occurrence` is abstract, so
 * a concrete test subtype is introduced here.
 */

/** TestOcc — a concrete occurrence for exercising the log anatomy. */
sig TestOcc extends Occurrence {}

// The core loads: a causally ordered pair exists.
run unit_occ_loads {
  some disj a, b: TestOcc | occPrecedes[a, b]
} for 4 expect 1

// Occurrences inherit a strict TOTAL causal order (from one-per-tick + the Tick total order).
assert unit_occ_total { all disj a, b: TestOcc | occPrecedes[a, b] or occPrecedes[b, a] }
check unit_occ_total for 5 expect 0

// One occurrence per tick (the linearization fact is in force).
assert unit_occ_onePerTick { all disj a, b: TestOcc | a.tick != b.tick }
check unit_occ_onePerTick for 5 expect 0
