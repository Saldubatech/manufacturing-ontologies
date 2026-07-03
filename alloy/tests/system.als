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
open resources/inventory_item/inventory_pool
open resources/kanban_card/kanban_card           // transitively: card_cycle, processing_network

// The quantitative layers' premises (same assumption the module suites make).
fact ScalarPremises { groupAxioms and orderAxioms }   // group suffices: domain roots do additive arithmetic only (DT-011)

// Machine scope (DT-003): 5 State (print only — the op machine retired with DT-015 Phase B),
// 8 Signal, 8 Transition, 1 StateMachine, 0 Guard. 5 Int: the cycle region ranks reach 8.

// Smoke: the union of the live modules admits a consistent instance.
pred sys_modelLoads {}
run sys_modelLoads
  for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 1

// Cross-domain: a card references an Item — and by kernel isolation they share a tenant.
pred sys_cardReferencesItem { some c: KanbanCard, i: Item | resolve[c.itemRef] = i }
run sys_cardReferencesItem
  for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 1

// Cross-domain composition: a card and an InventoryItem classified by the SAME Item coexist
// (the KanbanCard ↔ InventoryItem seam meets at reference data).
pred sys_cardAndHoldingShareItem {
  some k: KanbanCard, ii: InventoryItem, i: Item | resolve[k.itemRef] = i and resolve[ii.itemRef] = i
}
run sys_cardAndHoldingShareItem
  for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 1

// Cross-domain isolation: a received material can never resolve to an InventoryItem of another
// tenant (materials are RECORD-carried since DT-015 Phase B — the tenancy law is the log-side
// ReceivedMaterialsIntegrity fact, exercised here across the composed modules).
pred sys_crossTenantMaterial {
  some o: ReceiveOcc | some m: resolve[o.materials] & InventoryItem | m.tenantId != o.cycle.tenantId
}
run sys_crossTenantMaterial
  for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// Pools participate in the composed model: a pool holding a member whose Item resolves in-tenant
// (membership read via the log projection — the pool is log-carried since 2026-07-02).
pred sys_poolHoldsClassifiedMember {
  some p: InventoryPool, t: Tick, i: Item |
    some ii: heldAt[p, t] | resolve[ii.itemRef] = i and p.tenantId = i.tenantId
}
run sys_poolHoldsClassifiedMember
  for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 1
