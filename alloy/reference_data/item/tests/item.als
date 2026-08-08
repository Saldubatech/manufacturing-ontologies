module reference_data/item/tests/item

open meta/kernel
open reference_data/item/item_implementation

// Item-module verification: Item + its child ItemSupply (structure only). The cross-module
// supply→supplier reference chain is verified in reference_data/shared/tests (it spans both modules).

// An Item with an ItemSupply child exists — the module is not over-constrained.
pred coherent { some i: Item, s: ItemSupply | s in i.supplies }
run unit_item_coherent { coherent } for 6 expect 1

// ItemSupply child ownership is exclusive — UNSAT = holds.
check unit_item_supplyOwnership {
  no c: ItemSupply | some disj i1, i2: Item | c in i1.supplies and c in i2.supplies
} for 6 expect 0

// ── Inventory-tracking mode & UoM scheme (DT-009) ───────────────────────────────────────────────
// A tracked Item exists with a multi-unit scheme (`each` + another configured unit).
run unit_item_trackedScheme {
  some i: Item | inventoryTracked[i] and some u: i.uom.units | u != Each
} for 6 expect 1

// A tracked and a non-tracked Item coexist (the mode is per-Item).
run unit_item_modesCoexist {
  some i, j: Item | inventoryTracked[i] and not inventoryTracked[j]
} for 6 expect 1

// Every scheme configures `each` with factor 1.0 — regression on UomSchemeWF.
check unit_item_eachConfigured {
  all s: UomScheme | some s.factor[Each] and s.factor[Each] = SOne
} for 6 expect 0

// Converting an amount already in `each` is the identity (factor 1.0) — needs the ring identity.
check unit_item_toEachIdentity {
  ringAxioms implies all s: UomScheme, amt: Scalar | toEach[s, Each, amt] = amt
} for 6 but 3 Scalar expect 0

// ── CUT 6 (DT-022 TQ-4 qualification, MP 2026-08-08) ────────────────────────────────────────────
// An Item may carry the card-issuance minimum default (copy-at-mint with operator override —
// caller-side; no law reads it). Distinct from the BANNED InventoryItem minimum (§8.6.2(iv)).
run unit_item_cardMinimumDefault {
  some i: Item | some i.cardMinimumQuantity
} for 5 expect 1
