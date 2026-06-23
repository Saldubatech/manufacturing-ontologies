module tests/system

// Whole-system / cross-domain suite. Opens every defined module; sys_* commands.
open meta/util
open resources/item_type
open resources/station
open resources/operator
open resources/loop
open resources/kanban_card
open resources/job
open resources/inventory_item

// Smoke: the union of all modules admits a consistent instance.
pred sys_modelLoads {}
run sys_modelLoads for 4 but 8 Int
