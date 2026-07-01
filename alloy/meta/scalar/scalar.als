module meta/scalar/scalar

/*
 * Scalar — the model's foundational NUMERIC primitive: a decimal/real value (an amount, or a
 * dimensionless factor that scales one). Alloy has no reals/floats, so `Scalar` is UNINTERPRETED and its
 * arithmetic is the reified ring operations below; the model verifies the algebraic STRUCTURE (the ring
 * and order laws, and everything built on them), not concrete decimal values. A concrete, implementable
 * bounded fixed-point realization is `meta/keyed_value_algebra/scalar_int` (the witness).
 *
 * Lives in its own module so every quantitative layer (the keyed value algebra over `key -> Scalar`,
 * Money/Quantity, measurement) shares one number type. See the design write-up
 * `design/meta/kernel/scalar.md` and the practice note `modeling/scalar-arithmetic.md`.
 * Reference: common-module Money.kt; DT-004/DT-005.
 */

/** Scalar — a decimal/real value: an amount or a scalar factor. Uninterpreted (Alloy has
    no reals); its arithmetic is the reified ring operations. */
sig Scalar {
  splus: Scalar -> one Scalar,    // a.splus[b] = a + b
  smul:  Scalar -> one Scalar,    // a.smul[b]  = a * b
  sneg:  one Scalar               // additive inverse, −a
}
one sig SZero in Scalar {}        // additive identity (0)
one sig SOne  in Scalar {}        // multiplicative identity (1)

// (Scalar, splus, smul) is a non-trivial commutative ring with unit. Stated as a PREMISE predicate,
// NOT a global fact: the keyed-algebra law checks assume it (`ringAxioms implies <law>`), but modules
// that merely CARRY Scalar-valued maps (Money/Quantity and their users) do not pay to solve a ring.
pred ringAxioms {
  SZero != SOne
  all a, b: Scalar      | a.splus[b] = b.splus[a]
  all a, b, c: Scalar   | (a.splus[b]).splus[c] = a.splus[b.splus[c]]
  all a: Scalar         | a.splus[SZero] = a
  all a: Scalar         | a.splus[a.sneg] = SZero
  all a, b: Scalar      | a.smul[b] = b.smul[a]
  all a, b, c: Scalar   | (a.smul[b]).smul[c] = a.smul[b.smul[c]]
  all a: Scalar         | a.smul[SOne] = a
  all a: Scalar         | a.smul[SZero] = SZero
  all a, b, c: Scalar   | a.smul[b.splus[c]] = (a.smul[b]).splus[a.smul[c]]
}
