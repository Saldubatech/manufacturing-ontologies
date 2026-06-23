module meta/examples/ex13_keyed_value_algebra

/*
 * PATTERN:  Totalling values across incompatible keys WITHOUT conversion — the free
 *           module / "MultiMoney" algebra. Same-key amounts sum; different keys coexist
 *           (widen); a key netting to zero drops (collapse); scale by a decimal factor.
 * UML:      n/a — a value-type algebra.
 * FP:       a finitely-supported map key → amount; an abelian group / ℤ-module under +, ·.
 * USE WHEN:  summing money in several currencies, or quantities in several units, when no
 *           exchange/conversion table is available.
 * AVOID:     forcing everything to one key (a silent wrong conversion), or failing on
 *           mixed keys. The algebra is total — it widens instead.
 * SEE ALSO:  meta/algebra/keyed_monoid; common-module Money.kt; DT-005 / money-quantity-algebra.md.
 *
 * A value is a normal-form map  key -> lone Scalar  (no zero entries). Choosing the key
 * type instantiates the algebra:  MultiMoney = Currency -> lone Scalar ;
 * MultiQuantity = Unit -> lone Scalar.  `Scalar` is an abstract decimal (Alloy has no
 * reals), so amounts and scalar factors are both decimals.
 */

open meta/algebra/keyed_monoid

// Two independent key types — currencies (money) and units of measure (quantity).
sig Currency {}   // e.g. USD, EUR
sig Unit {}       // e.g. KG, EACH

// Revenue booked in two currencies can't be collapsed without an FX rate — it stays a
// two-currency MultiMoney (widen).
run multiCurrencyTotal {
  some usd, eur: Currency -> lone Scalar |
    isSingle[usd] and isSingle[eur] and usd.Scalar != eur.Scalar and isMulti[add[usd, eur]]
} for 3 but exactly 3 Scalar, exactly 2 Currency, exactly 2 Unit

// Quantities in different units likewise cannot be added into one number (widen).
run multiUnitQuantity {
  some kg, each: Unit -> lone Scalar |
    isSingle[kg] and isSingle[each] and kg.Scalar != each.Scalar and isMulti[add[kg, each]]
} for 3 but exactly 3 Scalar, exactly 2 Currency, exactly 2 Unit

// A booking and its reversal net to zero (collapse).
run reversalCollapses {
  some m: Currency -> lone Scalar | isSingle[m] and isZero[add[m, negate[m]]]
} for 3 but exactly 3 Scalar, exactly 2 Currency, exactly 2 Unit

// Scaling by the zero decimal annihilates; by one is the identity.
run scaleByZero { some m: Currency -> lone Scalar | isSingle[m] and isZero[scale[SZero, m]] }
  for 3 but exactly 3 Scalar, exactly 2 Currency, exactly 2 Unit
run scaleByOne  { some m: Currency -> lone Scalar | isSingle[m] and scale[SOne, m] = m }
  for 3 but exactly 3 Scalar, exactly 2 Currency, exactly 2 Unit
