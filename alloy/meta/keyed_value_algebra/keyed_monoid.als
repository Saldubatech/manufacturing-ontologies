module meta/keyed_value_algebra/keyed_monoid

/*
 * WHAT THIS OFFERS A DOMAIN MODELER (DT-013): a well-defined set of operations (add, scale,
 * negate, zero) on DISPARATE EXPRESSIONS of the same underlying concept — amounts spread across
 * currencies (Money) or units (Quantity) — without ever converting between the keys.
 *
 * Implementation: a keyed additive group with scalar multiplication — the algebra behind
 * common-module's GeneralizedMoney / MultiMoney (cards.arda.common.lib.domain.general.Money).
 *
 * A value is a finitely-supported, NORMAL-FORM map  key -> Scalar : the relation
 * `univ -> lone Scalar` carrying no zero-valued entries (each key appears at most once
 * and only with a non-zero amount). This is the free module over the keys; "adding
 * values whose keys differ, with no conversion" = staying in this direct sum: same key
 * sums, different keys coexist (widen), a key netting to zero drops (collapse).
 * Instantiate by choosing the key type:  MultiMoney = Currency -> lone Scalar ;
 * MultiQuantity = Unit -> lone Scalar.
 *
 * `Scalar` (the decimal/real carrier + its reified ring ops + `ringAxioms`) is the foundational numeric
 * primitive, now its own module `meta/scalar/scalar` (opened below). This module is the KEYED structure
 * over it (widen / collapse / normal form); it verifies that, not decimal arithmetic itself.
 * Reference: Money.kt. See DT-004 / DT-005; design/meta/kernel/scalar.md.
 */

open meta/scalar/scalar   // Scalar, splus/smul/sneg, SZero, SOne, ringAxioms

// The additive identity value — the empty (key-less) map (common-module's `ZeroMoney`).
fun zero: univ -> lone Scalar { none -> none }

// Normal form: no key maps to the zero scalar (zeros are dropped, never stored).
pred nf[a: univ -> lone Scalar] { no k: univ | a[k] = SZero }

// Pointwise addition: same-key amounts sum, different keys coexist (widen), a key whose
// total nets to zero drops (collapse). Result is in normal form.
//
// Alloy syntax: the body is a SET COMPREHENSION `{ k: univ, v: Scalar | … }` — it builds
// the result relation as the (key, amount) pairs satisfying the condition. `a[k]` is the
// "box join" (= `k.a`) = the lone amount a assigns to k (empty if k is absent).
// `a[k].splus[b[k]]` applies the scalar ring's `+`. The three disjuncts cover: present in
// both (sum), only in a, only in b. `v != SZero` drops a key whose total nets to zero.
fun add[a, b: univ -> lone Scalar]: univ -> lone Scalar {
  { k: univ, v: Scalar |
      v != SZero and
      ( (some a[k] and some b[k] and v = a[k].splus[b[k]])
        or (some a[k] and no b[k] and v = a[k])
        or (no a[k] and some b[k] and v = b[k]) ) }
}

// Scalar multiplication by a dimensionless decimal. scale[SZero,a] = zero (absorbing);
// scale[s, zero] = zero.
fun scale[s: Scalar, a: univ -> lone Scalar]: univ -> lone Scalar {
  { k: univ, v: Scalar | some a[k] and v = s.smul[a[k]] and v != SZero }
}

// Additive inverse.
fun negate[a: univ -> lone Scalar]: univ -> lone Scalar {
  { k: univ, v: Scalar | some a[k] and v = a[k].sneg and v != SZero }
}

// Classification — common-module's ZeroMoney / Money.Value / MultiMoney variants.
pred isZero  [a: univ -> lone Scalar] { no a }
pred isSingle[a: univ -> lone Scalar] { one a.Scalar }
pred isMulti [a: univ -> lone Scalar] { gt[#(a.Scalar), 1] }
