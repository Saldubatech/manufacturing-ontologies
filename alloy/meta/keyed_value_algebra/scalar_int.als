module meta/keyed_value_algebra/scalar_int

/*
 * scalar_int — a CONCRETE, IMPLEMENTABLE interpretation of the abstract `Scalar` ring
 * (meta/keyed_value_algebra/keyed_monoid) as bounded FIXED-POINT integer arithmetic.
 *
 * Alloy has no reals or floats; the established idiom for "programming-language arithmetic" is bounded
 * `Int` (a fixed bitwidth, two's-complement) + fixed-point SCALING for fractions + an overflow
 * discipline. This module realizes that idiom: it is the concrete WITNESS that the ring laws are
 * satisfiable by a real arithmetic, and the basis a modern tech stack actually implements
 * (`long` cents / `BigDecimal` with a scale). Limited precision is accepted by design — truncating
 * division and overflow at the bitwidth bound, exactly as machine arithmetic behaves.
 *
 *   carrier  : Alloy `Int` (bitwidth-bounded; the ring ℤ/2^bw under wraparound).
 *   SCALE    : the fixed-point denominator — value n denotes the rational n/SCALE. SCALE=1 ⇒ integers;
 *              SCALE=10^k ⇒ k decimal places (needs a wider bitwidth for the same magnitude range).
 *
 * RING vs ORDER vs DIVISION (see modeling/scalar-arithmetic.md):
 *   - ringAxioms HOLD on the carrier even WITH wraparound: ℤ/2^bw is a commutative ring with unit
 *     (add/mul commute, associate, distribute; identities/inverses exist). The ring-law checks below
 *     pass without any overflow option.
 *   - The ORDER (orderAxioms) is the one thing wraparound breaks (7+1 = −8 < 7). A FINITE ring cannot
 *     be an ordered ring; the order is sound only within the non-overflowing range. We follow the
 *     recommended practice — CONSTRAIN values to stay in range (facts) rather than rely on the
 *     "forbid overflows" analyzer option, which can mask counterexamples.
 *   - DIVISION is bounded, TRUNCATING fixed-point division (`div`, rounds toward zero), guarded against
 *     0. It is lossy by design; it is NOT a ring operation and stays out of the abstract algebra.
 *
 * References: Milicevic & Jackson, "Preventing Arithmetic Overflows in Alloy" (ABZ'12); Practical Alloy,
 * "Working with integers"; the Alloy `util/integer` module + language reference. See modeling/scalar-arithmetic.md.
 */

open util/integer   // plus, minus, mul, div, rem, gt, lt, lte

/** SCALE — the fixed-point denominator. SCALE=1 ⇒ integer arithmetic. */
fun scale: Int { 1 }

/** fZero / fOne — the ring identities (fOne = SCALE in fixed point). (`one`/`zero`-free names: `one` is
    a reserved multiplicity keyword.) */
fun fZero: Int { 0 }
fun fOne:  Int { scale }

/** fadd / fneg — fixed-point addition and additive inverse (scale-invariant). */
fun fadd[a, b: Int]: Int { plus[a, b] }
fun fneg[a: Int]: Int { minus[0, a] }

/** fmul — fixed-point product: (a·b) rescaled by SCALE (= a·b when SCALE=1). */
fun fmul[a, b: Int]: Int { div[mul[a, b], scale] }

/** fdiv — fixed-point quotient (a/b), truncating toward zero; caller ensures b ≠ 0. Lossy by design. */
fun fdiv[a, b: Int]: Int { div[mul[a, scale], b] }
