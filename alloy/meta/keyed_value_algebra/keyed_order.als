module meta/keyed_value_algebra/keyed_order

/*
 * ORDER, SIGN CLASSIFICATION, and (partial) EQUALITY for the keyed monoid
 * (meta/keyed_value_algebra/keyed_monoid). This is an OPTIONAL extension — open it only where you
 * need to compare values; the base monoid (add / scale) does not depend on it.
 *
 * ──────────────────────── The concepts (abstract algebra, plainly) ────────────────────
 * A monoid value is a map  key -> amount,  e.g. {USD↦3, EUR↦5}. There is NO single TOTAL
 * order on such values — 3 USD vs 5 EUR can't be ranked without an exchange rate. What we
 * CAN define:
 *
 *  • PARTIAL ORDER (the "product order"): A ≤ B iff A's amount ≤ B's amount on EVERY key
 *    (a missing key counts as 0). Comparable only when all components agree on direction;
 *    otherwise the two are INCOMPARABLE. e.g. {USD↦5,EUR↦2} ≤ {USD↦6,EUR↦2}, but
 *    {USD↦5} and {EUR↦3} are incomparable.
 *
 *  • SIGN CLASSIFICATION (4 classes, partitioning every value):
 *      ZERO          — the empty value
 *      POSITIVE      — every amount > 0   (≡ "strictly above ZERO" in the product order)
 *      NEGATIVE      — every amount < 0
 *      INDETERMINATE — mixed signs (some +, some −); your "Indeterminate".
 *    The coarse class order SP > ZERO > SN you sketched is SUBSUMED here: it falls out of
 *    the product order against ZERO.
 *
 *  • TWO EQUALITIES (your #3 — like languages with `==` vs `equals`):
 *      LEXICAL   — the maps are identical (ordinary set-equality of entries).
 *      SEMANTIC  — partial / 3-valued ("do they denote the same real amount?"):
 *          EQUAL        when the maps are identical;
 *          UNEQUAL      when they differ on EXACTLY ONE key (same unit ⇒ directly comparable
 *                       ⇒ definitely different);
 *          UNDETERMINED when they differ on TWO OR MORE keys — we'd need conversion to tell
 *                       whether the differences cancel ({3USD,5EUR} =?= {2USD}). A SEMANTIC
 *                       indeterminacy, not a floating-point / precision issue.
 *
 * ──────────────────────── Why the order is POSITED, not derived ───────────────────────
 * Comparing amounts needs an order on `Scalar`. A genuine order on a ring forces
 * 1 < 1+1 < 1+1+1 < … — infinitely many elements — so no FINITE `Scalar` can carry a
 * ring-COMPATIBLE order, and Alloy reasons over finite universes (and has no real/float
 * type — only bounded `Int`). So we POSIT an abstract linear order `ScalarOrder.le` as a
 * PREMISE (`orderAxioms`): on a finite set a linear order always exists, so it is
 * satisfiable. We can DEFINE and USE comparison/sign/equality with it, and the
 * value-level partial-order LAWS hold; we just cannot PROVE the order interacts with `+`
 * (positive + positive = positive) — that needs the infinite case, so we ASSUME it, just
 * as we assume the ring axioms.
 */

open meta/keyed_value_algebra/keyed_monoid

// ── The posited order on Scalar ───────────────────────────────────────────────────────
// `le` is a binary relation read as "≤": the tuple `a->b` being `in le` means a ≤ b.
// (Alloy syntax: `a -> b` is an ordered pair; `in` is the subset/membership test; a
// relation `Scalar -> Scalar` is a set of such pairs.) We hang it on a `one sig` carrier
// (a single global object) rather than on `Scalar` itself, so the base monoid stays
// order-free.
one sig ScalarOrder { le: Scalar -> Scalar }

// PREMISE (like `ringAxioms` — NOT a global fact): `le` is a total order.
pred orderAxioms {
  all a: Scalar | a -> a in ScalarOrder.le                                                  // reflexive
  all a, b: Scalar | (a -> b in ScalarOrder.le and b -> a in ScalarOrder.le) implies a = b  // antisymmetric
  all a, b, c: Scalar |
    (a -> b in ScalarOrder.le and b -> c in ScalarOrder.le) implies a -> c in ScalarOrder.le // transitive
  all a, b: Scalar | a -> b in ScalarOrder.le or b -> a in ScalarOrder.le                    // total
}

// "a ≤ b" on single scalars.
pred sLeq[a, b: Scalar] { a -> b in ScalarOrder.le }

// The strictly-positive / strictly-negative scalars, relative to SZero (0).
// (Alloy syntax: `{ s: Scalar | P[s] }` is set comprehension — the set of scalars
// satisfying P.)
fun positives: set Scalar { { s: Scalar | s != SZero and sLeq[SZero, s] } }
fun negatives: set Scalar { { s: Scalar | s != SZero and sLeq[s, SZero] } }

// ── Value-level helpers ────────────────────────────────────────────────────────────────
// The amount a value assigns to key k, treating a MISSING key as SZero (0). `a[k]` is the
// "box join" (= k.a) — the lone amount at k; `cond => x else y` is Alloy's if-then-else.
fun at[a: univ -> lone Scalar, k: univ]: one Scalar { some a[k] => a[k] else SZero }

// All amounts appearing in a value (its range). `univ.a` joins every atom with `a`.
fun amounts[a: univ -> lone Scalar]: set Scalar { univ.a }

// ── Partial order on values (the product order) ─────────────────────────────────────────
// A ≤ B iff, on every key present in either, A's amount ≤ B's amount. (`a.Scalar` is the
// DOMAIN of a — its keys; `+` here is set UNION of the two key sets.)
pred lte[a, b: univ -> lone Scalar] {
  all k: a.Scalar + b.Scalar | sLeq[at[a, k], at[b, k]]
}

// ── Sign classification ─────────────────────────────────────────────────────────────────
// `enum` declares a fixed set of named constants (each a singleton). Members are GLOBAL,
// so they are named to avoid clashes with the `positives`/`negatives` functions above.
enum Sign { ZERO, POSITIVE, NEGATIVE, INDETERMINATE }

fun classify[a: univ -> lone Scalar]: one Sign {
  isZero[a]              => ZERO
  else amounts[a] in positives => POSITIVE          // all amounts strictly positive
  else amounts[a] in negatives => NEGATIVE          // all amounts strictly negative
  else INDETERMINATE                                // mixed signs
}

// ── Equality ────────────────────────────────────────────────────────────────────────────
// LEXICAL: the maps are identical (ordinary relation equality).
pred lexEq[a, b: univ -> lone Scalar] { a = b }

// SEMANTIC (partial, 3-valued), computed from the SUPPORT of the difference a − b:
//   no keys differ → EQUAL ; exactly one key differs → UNEQUAL ; two or more → UNDETERMINED.
enum EqVerdict { EQUAL, UNEQUAL, UNDETERMINED }

fun semanticEq[a, b: univ -> lone Scalar]: one EqVerdict {
  let d = add[a, negate[b]] |          // d = a − b, in normal form
    isZero[d]   => EQUAL               // identical
    else isSingle[d] => UNEQUAL        // differ on one key (same unit ⇒ definitely ≠)
    else UNDETERMINED                  // differ on ≥2 keys ⇒ need conversion to decide
}
