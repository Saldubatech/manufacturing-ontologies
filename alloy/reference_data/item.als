module reference_data/item

open meta/kernel
open reference_data/item_supply

// Reference data for a material / product. Tenant-scoped entity.
sig Item extends Scoped {
  supplies:      set ItemSupply,   // parent → child aggregation (no backref)
  defaultSupply: lone EntityId      // soft ref → one of this item's ItemSupply
}

// Every ItemSupply belongs to exactly one Item and inherits its tenant; the default
// supply, if resolved, is one of this item's own supplies.
fact ItemSupplyOwnership {
  all c: ItemSupply | one i: Item | c in i.supplies
  all i: Item, c: i.supplies | c.tenantId = i.tenantId
  all i: Item | let d = resolve[i.defaultSupply] | some d implies d in i.supplies
}

// Outgoing soft references (the parent→child `supplies` is a direct relation, not a
// soft ref, and is already kept in-tenant by ItemSupplyOwnership).
fact ItemRefs { all i: Item | i.refs = i.defaultSupply }
