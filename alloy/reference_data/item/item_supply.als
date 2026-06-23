module reference_data/item/item_supply

open meta/kernel
open meta/values
open reference_data/business_affiliate/business_affiliate   // SupplierReference (+ BusinessRole, transitively, for the integrity fact)

/** OrderMethod — how an item is ordered from a supplier. */
enum OrderMethod {
  UNKNOWN, PURCHASE_ORDER, EMAIL, PHONE, IN_STORE, ONLINE, RFQ, PRODUCTION, TASK, THIRD_PARTY, OTHER
}

/** ItemSupply — a supply source for an Item (vendor, order method, cost, lead time);
    a child entity of Item, first-class as the target of Item.defaultSupply. */
sig ItemSupply extends Scoped {
  supplier:        one SupplierReference,
  orderMethod:     lone OrderMethod,
  orderQuantity:   lone Quantity,
  unitCost:        lone Money,
  averageLeadTime: lone Duration
}

// Referential integrity (item depends-on business_affiliate — allowed): if a
// supplier's vendor ref resolves in scope, the target must be a VENDOR BusinessRole.
// Dangling/unresolved refs are allowed — that is the 'soft' (cross-Universe) case.
fact SupplierRefIsVendor {
  all s: ItemSupply | let v = resolve[s.supplier.vendorRef] |
    some v implies (v in BusinessRole and v.role = VENDOR)
}

// Outgoing soft references, for the kernel's generic cross-reference rules.
fact ItemSupplyRefs {
  all s: ItemSupply | s.dataRefs = s.supplier.vendorRef + s.supplier.affiliateRef
}

// Tight by default (see modeling-conventions §6): a resolved affiliateRef is a
// BusinessAffiliate, and the resolved vendor role belongs to that affiliate.
fact SupplierRefIntegrity {
  all s: ItemSupply |
    let ar = resolve[s.supplier.affiliateRef], vr = resolve[s.supplier.vendorRef] {
      some ar implies ar in BusinessAffiliate
      (some vr and some ar) implies vr in ar.roles
    }
}

// Tight by default: no orphan value/handle atoms. Money/Duration/SupplierReference
// remain ItemSupply-exclusive, so their no-orphan rules stay here.
// Quantity became SHARED with KanbanCard — the §6 forcing function fired: its
// no-orphan rule was relocated up to resources/kanban_card, the lowest module in the
// open-DAG that sees all Quantity users. (See modeling-conventions §6.)
fact NoOrphanSupplierReference { all sr: SupplierReference | sr in ItemSupply.supplier }
fact NoOrphanItemSupplyValues {
  all m: Money    | m in ItemSupply.unitCost
  all d: Duration | d in ItemSupply.averageLeadTime
}
