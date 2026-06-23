module tests/system

// Whole-system / cross-domain suite for the live entity model; sys_* commands.
// (The X.731 behavioral spike was archived to alloy-sample/kanban_sim/.)
open meta/kernel
open reference_data/item       // transitively: item_supply, business_affiliate, business_role
open resources/kanban_card

// Smoke: the union of the live modules admits a consistent instance.
pred sys_modelLoads {}
run sys_modelLoads for 6 but 5 Int

// Cross-domain: a card references an Item — and by kernel isolation they share a tenant.
pred sys_cardReferencesItem { some c: KanbanCard, i: Item | resolve[c.itemRef] = i }
run sys_cardReferencesItem for 6 but 5 Int
