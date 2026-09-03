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

// The note seat: an occurrence may carry a free-text annotation of the act itself (plain
// String — zero universe cost in commands without literals; MP ruling 2026-08-10).
run unit_occ_noteWitness {
  some o: TestOcc | o.note = "expedited at the vendor's request"
} for 4 but exactly 1 String expect 1

// The note is genuinely optional — a noted and an un-noted occurrence coexist.
run unit_occ_noteOptional {
  some disj a, b: TestOcc | some a.note and no b.note
} for 4 but exactly 1 String expect 1

// The ORIGIN seat (DT-029 E1): absence reads as self-minted — exactly one representation of "no caller".
run unit_occ_archeOfSelfMinted {
  some o: TestOcc | no o.arche and archeOf[o] = o
} for 4 expect 1

// An origin is strictly earlier than the occurrence citing it.
assert unit_occ_archeOriginPrecedes { all o: TestOcc | some o.arche implies occPrecedes[o.arche, o] }
check unit_occ_archeOriginPrecedes for 5 expect 0

// A self-citation is unrepresentable — "self-minted" cannot be spelled as a loop (negative run).
run unit_occ_archeSelfCiteImpossible {
  some o: TestOcc | o.arche = o
} for 4 expect 0

// The field is genuinely optional: a cited origin and an uncited (self-minted) occurrence coexist.
run unit_occ_archeOptional {
  some disj a, b: TestOcc | a.arche = b and no b.arche
} for 4 expect 1
