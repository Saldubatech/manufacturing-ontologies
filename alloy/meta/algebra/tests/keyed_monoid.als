module meta/algebra/tests/keyed_monoid

open meta/algebra/keyed_monoid

// Uninterpreted test keys — the algebra holds for an arbitrary key type. `exactly 3
// Scalar` pins the abstract ring to a 3-element commutative ring with unit (ℤ/3).

sig K {}

// --- demonstrations of the behaviour (existential) ---
run unit_alg_loads { some Scalar } for 3 but exactly 3 Scalar

// widen: two single-key values on DIFFERENT keys add to a multi-key value
run unit_alg_widen {
  some a, b: K -> lone Scalar |
    isSingle[a] and isSingle[b] and a.Scalar != b.Scalar and isMulti[add[a, b]]
} for 3 but exactly 3 Scalar

// collapse: a value plus its negation nets to zero
run unit_alg_collapse {
  some a: K -> lone Scalar | isSingle[a] and isZero[add[a, negate[a]]]
} for 3 but exactly 3 Scalar

// scale by the zero scalar annihilates to zero; scale by one is the identity
run unit_alg_scaleZero { some a: K -> lone Scalar | isSingle[a] and isZero[scale[SZero, a]] } for 3 but exactly 3 Scalar
run unit_alg_scaleOne  { some a: K -> lone Scalar | isSingle[a] and scale[SOne, a] = a } for 3 but exactly 3 Scalar

// --- keyed-algebra laws (universal; small scope) ---
check unit_alg_addCommutative {
  all a, b: K -> lone Scalar | (nf[a] and nf[b]) implies add[a, b] = add[b, a]
} for 3 but exactly 3 Scalar

check unit_alg_addIdentity {
  all a: K -> lone Scalar | nf[a] implies add[a, zero] = a
} for 3 but exactly 3 Scalar

check unit_alg_addClosedNf {
  all a, b: K -> lone Scalar | (nf[a] and nf[b]) implies nf[add[a, b]]
} for 3 but exactly 3 Scalar

check unit_alg_addAssociative {
  all a, b, c: K -> lone Scalar |
    (nf[a] and nf[b] and nf[c]) implies add[add[a, b], c] = add[a, add[b, c]]
} for 3 but exactly 3 Scalar

check unit_alg_addInverse {
  all a: K -> lone Scalar | nf[a] implies add[a, negate[a]] = zero
} for 3 but exactly 3 Scalar

check unit_alg_scaleZeroScalar { all a: K -> lone Scalar | scale[SZero, a] = zero } for 3 but exactly 3 Scalar
check unit_alg_scaleZeroValue  { all s: Scalar | scale[s, zero] = zero } for 3 but exactly 3 Scalar
check unit_alg_scaleOneIdentity { all a: K -> lone Scalar | nf[a] implies scale[SOne, a] = a } for 3 but exactly 3 Scalar

check unit_alg_scaleDistribAdd {
  all s: Scalar, a, b: K -> lone Scalar |
    (nf[a] and nf[b]) implies scale[s, add[a, b]] = add[scale[s, a], scale[s, b]]
} for 3 but exactly 3 Scalar
