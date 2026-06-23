module meta/values

/*
 * Universal value objects (no identity; equal-by-content). Money and Quantity are
 * INSTANCES of the keyed monoid (meta/algebra/keyed_monoid): a value is a normal-form
 * map  key -> lone Scalar  with the monoid's add / scale / negate / zero.
 *   Money    = the Currency-keyed instance  (MultiMoney)
 *   Quantity = the Unit-keyed instance       (MultiQuantity)
 * Alloy has no type aliases, so each is a thin sig wrapping its normal-form map; the
 * monoid operations apply to that map (e.g. `add[m1.byCurrency, m2.byCurrency]`).
 * Amounts are decimals (abstract Scalar). Duration stays opaque for now (a future
 * time-unit monoid); the QUDT bridge for Unit/Currency is deferred (DT-002, DT-005).
 */
open meta/algebra/keyed_monoid   // Scalar, nf, add, scale, negate, zero, isZero/isSingle/isMulti

// --- monoid key types -------------------------------------------------------
// Money key — real currencies are common-module Currency.kt (USD, EUR, …); opaque here.
sig Currency {}
// Quantity key — a unit of measure; opaque now (QUDT bridge later, DT-002).
sig Unit {}

// --- Money: the Currency-keyed monoid instance (MultiMoney) -----------------
// A value spanning one or more currencies (no conversion); normal form (no zero entries).
sig Money { byCurrency: Currency -> lone Scalar } { nf[byCurrency] }
// Value semantics: a Money IS its amounts — no two Money atoms share the same map.
fact MoneyExtensional { all disj a, b: Money | a.byCurrency != b.byCurrency }

// --- Quantity: the Unit-keyed monoid instance (MultiQuantity) ---------------
sig Quantity { byUnit: Unit -> lone Scalar } { nf[byUnit] }
fact QuantityExtensional { all disj a, b: Quantity | a.byUnit != b.byUnit }

// --- still opaque -----------------------------------------------------------
// A length of time. (A future time-unit monoid; QUDT bridge deferred, DT-002.)
sig Duration {}

// --- PhysicalLocator: a containment hierarchy of physical space ------------
// Nine nesting levels, outermost → innermost. All optional opaque labels (code: String);
// the `facility` module will model this richly later. Two locators with the same values
// denote the EXACT SAME physical space (containment is implicit for now).
sig Label {}
sig PhysicalLocator {
  region:   lone Label,
  facility: lone Label,
  area:     lone Label,
  aisle:    lone Label,
  bay:      lone Label,
  shelf:    lone Label,
  tier:     lone Label,
  slot:     lone Label,
  bin:      lone Label
}

// A locator names at least one level (it must point somewhere). The full containment
// chain (a bin sits within a slot within a tier …) is deferred to the facility module.
fact LocatorNonEmpty {
  all p: PhysicalLocator |
    some (p.region + p.facility + p.area + p.aisle + p.bay + p.shelf + p.tier + p.slot + p.bin)
}

// Tight by default: no orphan labels — every Label is used at some locator level.
fact NoOrphanLabel {
  all l: Label | l in PhysicalLocator.(region + facility + area + aisle + bay + shelf + tier + slot + bin)
}
