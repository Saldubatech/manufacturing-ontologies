module tests/system

// Whole-system / cross-domain suite for the live entity model; sys_* commands.
// Re-pointed 2026-07-01 from the kanban BASELINE to the current split model (KC-MH-9): this root now
// composes reference_data + inventory_item + inventory_pool + KanbanCard/CardCycle. The baseline keeps
// its own suite (resources/kanban_card/baseline/tests/). Opening inventory_item makes this a TEMPORAL
// root (var fields); the cross-domain invariants below constrain IMMUTABLE relations only, so they stay
// bare (modeling-conventions §3.2).
open meta/kernel
open meta/keyed_value_algebra/keyed_order   // ringAxioms/orderAxioms (no longer re-exported by the slimmed inventory_item — DT-011)
open reference_data/item/item                    // transitively: item_supply, business_affiliate, business_role
open resources/inventory_item/inventory_item
open resources/inventory_pool/inventory_pool
open resources/kanban_card/kanban_card           // transitively: card_cycle, processing_network

// The quantitative layers' premises (same assumption the module suites make).
fact ScalarPremises { ringAxioms and orderAxioms }

// Machine scope (DT-003): 14 State (9 op + 5 print), 20 Signal, 20 Transition, 2 StateMachine, 0 Guard.

// Smoke: the union of the live modules admits a consistent instance.
pred sys_modelLoads {}
run sys_modelLoads
  for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 1

// Cross-domain: a card references an Item — and by kernel isolation they share a tenant.
pred sys_cardReferencesItem { some c: KanbanCard, i: Item | resolve[c.itemRef] = i }
run sys_cardReferencesItem
  for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 1

// Cross-domain composition: a card and an InventoryItem classified by the SAME Item coexist
// (the KanbanCard ↔ InventoryItem seam meets at reference data).
pred sys_cardAndHoldingShareItem {
  some k: KanbanCard, ii: InventoryItem, i: Item | resolve[k.itemRef] = i and resolve[ii.itemRef] = i
}
run sys_cardAndHoldingShareItem
  for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 1

// Cross-domain isolation: a cycle's material can never resolve to an InventoryItem of another tenant
// (kernel CrossTenantIsolation composed across three modules; immutable relations — bare, §3.2).
pred sys_crossTenantMaterial {
  some c: CardCycle, m: c.materials | let ii = resolve[m] |
    some ii and ii in InventoryItem and ii.tenantId != c.tenantId
}
run sys_crossTenantMaterial
  for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// Pools participate in the composed model: a pool holding a member whose Item resolves in-tenant.
pred sys_poolHoldsClassifiedMember {
  some p: InventoryPool, ii: p.items, i: Item | resolve[ii.itemRef] = i and p.tenantId = i.tenantId
}
run sys_poolHoldsClassifiedMember
  for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 1
