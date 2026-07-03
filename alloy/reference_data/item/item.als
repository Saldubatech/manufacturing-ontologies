module reference_data/item/item

open meta/profiles/baseline          // PROFILE (DT-012): structural — identity/refs/tenancy
open meta/kernel
open reference_data/item/item_supply
open reference_data/item/uom            // UomScheme, Each — inventory-tracking mode (DT-009)

/** Item — reference-data master for a material/product (the TYPE); InventoryItems and
    supply records classify against it. Tenant-scoped. */
sig Item extends Scoped {
  supplies:      set ItemSupply,   // parent → child aggregation (no backref)
  defaultSupply: lone EntityId,     // soft ref → one of this item's ItemSupply
  uom:           lone UomScheme     // present ⟺ inventory-TRACKED (DT-009); immutable (no mode change)
}

/** inventoryTracked — an Item is inventory-tracked iff it carries a UoM scheme (enforced UoM +
    conversions; total min/max/zero/capacity). Otherwise non-tracked (any unit; keyed MultiQuantity
    only; partial comparisons). DT-009. */
pred inventoryTracked[i: Item] { some i.uom }

// Each UomScheme belongs to exactly one Item (no orphan schemes).
fact UomSchemeOwnership { all s: UomScheme | one i: Item | i.uom = s }

// Every ItemSupply belongs to exactly one Item and inherits its tenant; the default
// supply, if resolved, is one of this item's own supplies.
fact ItemSupplyOwnership {
  all c: ItemSupply | one i: Item | c in i.supplies
  all i: Item, c: i.supplies | c.tenantId = i.tenantId
  all i: Item | let d = resolve[i.defaultSupply] | some d implies d in i.supplies
}

// Outgoing soft references (the parent→child `supplies` is a direct relation, not a
// soft ref, and is already kept in-tenant by ItemSupplyOwnership).
fact ItemRefs { all i: Item | i.dataRefs = i.defaultSupply }
