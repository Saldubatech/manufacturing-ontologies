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

// The premises are LAYERED by what a consumer actually uses (DT-011 simplification, 2026-07-02):
// domain roots do only ADDITIVE arithmetic over keyed maps (add/negate/zero) — they assume
// `groupAxioms` (+ `orderAxioms` from keyed_order). Multiplication exists for SCALING/conversion
// only (keyed `scale`, the DT-009 uom collapse) — those roots assume the full `ringAxioms`.
// Both are PREMISE predicates, NOT global facts: modules that merely CARRY Scalar-valued maps
// (Money/Quantity and their users) do not pay to solve either.

/** groupAxioms — (Scalar, splus, SZero, sneg) is an abelian GROUP: everything the domain layers'
    additive quantity arithmetic needs. Assume this (+ orderAxioms) in domain roots. */
pred groupAxioms {
  all a, b: Scalar      | a.splus[b] = b.splus[a]
  all a, b, c: Scalar   | (a.splus[b]).splus[c] = a.splus[b.splus[c]]
  all a: Scalar         | a.splus[SZero] = a
  all a: Scalar         | a.splus[a.sneg] = SZero
}

/** ringAxioms — the full non-trivial commutative ring with unit: groupAxioms + multiplication.
    Needed ONLY where scaling/conversion multiplies (keyed `scale` laws, the uom collapse). */
pred ringAxioms {
  groupAxioms
  SZero != SOne
  all a, b: Scalar      | a.smul[b] = b.smul[a]
  all a, b, c: Scalar   | (a.smul[b]).smul[c] = a.smul[b.smul[c]]
  all a: Scalar         | a.smul[SOne] = a
  all a: Scalar         | a.smul[SZero] = SZero
  all a, b, c: Scalar   | a.smul[b.splus[c]] = (a.smul[b]).splus[a.smul[c]]
}
