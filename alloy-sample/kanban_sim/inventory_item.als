module kanban_sim/inventory_item

open kanban_sim/item_type   // ItemType
open kanban_sim/station     // Station

// A physical batch of material moving through the system. (Relocated; name kept.)
sig InventoryLot {
  lotItemType:        one ItemType,
  var currentStation: one Station
}
