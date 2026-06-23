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

// Tight by default (§6): a quantity is strictly positive. (Relax explicitly if a
// zero/negative quantity ever becomes meaningful — e.g. an adjustment delta.)
fact PositiveQuantity { all q: Quantity | q.amount > 0 }

// Tight by default: no orphan units — every Unit labels some Quantity. Self-contained
// (Unit is used only here). Relax when units gain a standalone catalog (QUDT bridge).
fact NoOrphanUnit { all u: Unit | u in Quantity.unit }

// --- PhysicalLocator: a hierarchical place within a facility ---------------
// facility > department > location > subLocation. `facility` is required; the lower
// levels are optional. Levels are opaque text handles (code: String).
sig Label {}
sig PhysicalLocator {
  facility:    one Label,
  department:  lone Label,
  location:    lone Label,
  subLocation: lone Label
}

// Tight by default: a sub-location presupposes a location (you cannot name a slot
// within an unnamed place). The code leaves the levels independently nullable, so
// this is a deliberate tightening to revisit if a flatter locator is ever needed.
fact LocatorHierarchy { all p: PhysicalLocator | some p.subLocation implies some p.location }

// Tight by default: no orphan labels — every Label is used at some locator level.
// Self-contained (Label is used only by PhysicalLocator).
fact NoOrphanLabel {
  all l: Label | l in PhysicalLocator.facility + PhysicalLocator.department
                    + PhysicalLocator.location + PhysicalLocator.subLocation
}
