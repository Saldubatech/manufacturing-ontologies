module meta/values

/*
 * Universal value objects (no identity; not entities). Money and Duration remain
 * opaque slots until the QUDT bridge (DT-002). Quantity and PhysicalLocator are
 * given structure now — they are needed, with real fields, by reference_data and
 * resources. No external-source linkage yet (DT-002).
 */

// --- Still opaque (QUDT bridge deferred) -----------------------------------
sig Money {}
sig Duration {}

// --- Quantity: a magnitude in a unit of measure ----------------------------
// `unit` is an opaque handle for now; it will bridge to a QUDT unit/quantity-kind
// in meta/std/qudt (DT-002). `amount` is modeled as an Int (an abstraction of the
// code's Double) so we can state a real constraint on it.
sig Unit {}
sig Quantity {
  amount: one Int,
  unit:   one Unit
}

// Quantities are non-negative. RELAXED from strictly-positive — the §6 forcing
// function fired: InventoryItem.actualQuantity can be zero (a depleted item). Specific
// uses may re-tighten locally (e.g. an order quantity should be > 0).
fact NonNegativeQuantity { all q: Quantity | q.amount >= 0 }

// Tight by default: no orphan units — every Unit labels some Quantity. Self-contained
// (Unit is used only here). Relax when units gain a standalone catalog (QUDT bridge).
fact NoOrphanUnit { all u: Unit | u in Quantity.unit }

// --- PhysicalLocator: a containment hierarchy of physical space ------------
// Nine nesting levels, outermost → innermost. All optional opaque labels (code:
// String); the `facility` module will model this richly later. Two locators with the
// same values denote the EXACT SAME physical space (containment is implicit for now).
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
// Self-contained (Label is used only by PhysicalLocator).
fact NoOrphanLabel {
  all l: Label | l in PhysicalLocator.(region + facility + area + aisle + bay + shelf + tier + slot + bin)
}
