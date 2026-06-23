module modules/quantity/quantity

open modules/core/core

/*
 * Physical quantities with units and quantity kinds. Alloy analogue of the
 * QUDT-backed owl/modules/quantity/quantity.ttl. Alloy cannot import QUDT, so
 * units and quantity kinds are modelled abstractly here, with a couple of
 * concrete singletons standing in for QUDT individuals.
 */

abstract sig Unit {}
abstract sig QuantityKind {}

sig PhysicalQuantity extends Entity {
  hasUnit:         one Unit,
  hasQuantityKind: one QuantityKind
}

-- Sample concrete unit / quantity kind (cf. qudt:unit/MilliM, qudt:quantitykind/Length)
one sig Millimetre extends Unit {}
one sig Length     extends QuantityKind {}
