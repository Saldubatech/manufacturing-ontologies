module meta/algebra/keyed_monoid

/*
 * Keyed additive group with scalar multiplication — the algebra behind common-module's
 * GeneralizedMoney / MultiMoney (cards.arda.common.lib.domain.general.Money).
 *
 * A value is a finitely-supported, NORMAL-FORM map  key -> Scalar : the relation
 * `univ -> lone Scalar` carrying no zero-valued entries (each key appears at most once
 * and only with a non-zero amount). This is the free module over the keys; "adding
 * values whose keys differ, with no conversion" = staying in this direct sum: same key
 * sums, different keys coexist (widen), a key netting to zero drops (collapse).
 * Instantiate by choosing the key type:  MultiMoney = Currency -> lone Scalar ;
 * MultiQuantity = Unit -> lone Scalar.
 *
 * `Scalar` abstracts a DECIMAL/REAL — amounts AND scalar factors are both decimals
 * (e.g. 0.5 * money). Alloy has no reals, so Scalar is uninterpreted and its arithmetic
 * is given by the operations + assumed commutative-ring axioms below; the model verifies
 * the KEYED structure (widen / collapse / normal form), not decimal arithmetic itself.
 * Reference: Money.kt. See DT-004 / money-quantity-algebra.md.
 */

// A decimal/real value — an amount or a scalar factor. Uninterpreted; arithmetic is the
// reified ring operations below.
sig Scalar {
  splus: Scalar -> one Scalar,    // a.splus[b] = a + b
  smul:  Scalar -> one Scalar,    // a.smul[b]  = a * b
  sneg:  one Scalar               // additive inverse, −a
}
one sig SZero in Scalar {}        // additive identity (0)
one sig SOne  in Scalar {}        // multiplicative identity (1)

// Assumed: (Scalar, splus, smul) is a non-trivial commutative ring with unit. (These are
// textbook for the reals; we assume rather than re-prove them, and check the keyed
// algebra on top.)
fact ScalarRing {
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

// The additive identity value — the empty (key-less) map (common-module's `ZeroMoney`).
fun zero: univ -> lone Scalar { none -> none }

// Normal form: no key maps to the zero scalar (zeros are dropped, never stored).
pred nf[a: univ -> lone Scalar] { no k: univ | a[k] = SZero }

// Pointwise addition: same-key amounts sum, different keys coexist (widen), a key whose
// total nets to zero drops (collapse). Result is in normal form.
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
