module reference_data/item_supply

open meta/kernel
open meta/values
open reference_data/business_affiliate   // SupplierReference (+ BusinessRole, transitively, for the integrity fact)

enum OrderMethod {
  UNKNOWN, PURCHASE_ORDER, EMAIL, PHONE, IN_STORE, ONLINE, RFQ, PRODUCTION, TASK, THIRD_PARTY, OTHER
}

// A supply source for an item. Child entity of Item (owned via Item.supplies).
// First-class because it is the target of Item.defaultSupply.
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

// Tight by default: no orphan value/handle atoms. Each must be attached to an
// ItemSupply. (These assume ItemSupply is the only user — relax/move explicitly when
// Money/Quantity/Duration/SupplierReference become shared across domains.)
fact NoOrphanSupplierReference { all sr: SupplierReference | sr in ItemSupply.supplier }
fact NoOrphanItemSupplyValues {
  all q: Quantity | q in ItemSupply.orderQuantity
  all m: Money    | m in ItemSupply.unitCost
  all d: Duration | d in ItemSupply.averageLeadTime
}
