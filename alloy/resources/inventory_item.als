module resources/inventory_item

open resources/item_type   // ItemType
open resources/station     // Station

// A physical batch of material moving through the system. (Relocated; name kept.)
sig InventoryLot {
  lotItemType:        one ItemType,
  var currentStation: one Station
}
