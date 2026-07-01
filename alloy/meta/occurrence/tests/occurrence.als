module meta/occurrence/tests/occurrence

open meta/occurrence/occurrence

/*
 * The bridge ties model time (`tick`) to domain time (`at`). The two clocks are INDEPENDENT unless the
 * `clocksAligned` premise is assumed — which is exactly what lets the model represent backdating.
 * `Occurrence` is abstract, so a concrete test subtype is introduced here.
 */

/** TestOcc — a concrete occurrence for exercising the bridge. */
sig TestOcc extends Occurrence {}

// A forward-aligned chain exists: two occurrences, causally ordered, with in-order domain stamps.
run unit_occ_loads {
  clocksAligned and (some disj a, b: TestOcc | occPrecedes[a, b] and earlierThan[a.at, b.at])
} for 4 expect 1

// Occurrences inherit a strict TOTAL causal order (from one-per-tick + the Tick total order).
assert unit_occ_total { all disj a, b: TestOcc | occPrecedes[a, b] or occPrecedes[b, a] }
check unit_occ_total for 5 expect 0

// BACKDATING is representable: WITHOUT `clocksAligned`, an occurrence causally BEFORE another may carry a
// LATER domain stamp. SAT = the two-axis model can express what a single fused axis cannot.
run unit_occ_backdating {
  some disj a, b: TestOcc | occPrecedes[a, b] and not atOrBefore[a.at, b.at]
} for 4 expect 1

// `clocksAligned` does its job: under the premise, no backdating is possible.
assert unit_occ_alignedForbidsBackdating {
  clocksAligned implies (no disj a, b: TestOcc | occPrecedes[a, b] and not atOrBefore[a.at, b.at])
}
check unit_occ_alignedForbidsBackdating for 5 expect 0

// One occurrence per tick (the linearization fact is in force).
assert unit_occ_oneePerTick { all disj a, b: TestOcc | a.tick != b.tick }
check unit_occ_oneePerTick for 5 expect 0
