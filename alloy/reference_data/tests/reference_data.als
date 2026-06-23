module reference_data/tests/reference_data

open meta/kernel
open reference_data/item/item
open reference_data/item/item_supply
open reference_data/business_affiliate/business_affiliate
open reference_data/business_affiliate/business_role

// A fully-linked, single-tenant instance exists — the model coheres and the
// reference chain Item → ItemSupply → SupplierReference → BusinessRole(VENDOR)
// is satisfiable (not over-constrained).
pred coherent {
  some i: Item, s: ItemSupply, ba: BusinessAffiliate, r: BusinessRole |
    s in i.supplies
    and r in ba.roles
    and r.role = VENDOR
    and s.supplier.vendorRef = r.eId          // supplier resolves to the vendor role
    and i.tenantId = ba.tenantId              // same tenant
}
run dom_referenceData_coherent { coherent } for 6

// Child ownership is exclusive (follows from the ownership facts) — UNSAT = holds.
assert dom_referenceData_ownershipExclusive {
  no c: ItemSupply | some disj i1, i2: Item | c in i1.supplies and c in i2.supplies
  no r: BusinessRole | some disj b1, b2: BusinessAffiliate | r in b1.roles and r in b2.roles
}
check dom_referenceData_ownershipExclusive for 6

// A resolved supplier reference is always a VENDOR role (follows from
// SupplierRefIsVendor) — UNSAT = holds.
assert dom_referenceData_supplierIsVendor {
  all s: ItemSupply | let v = resolve[s.supplier.vendorRef] |
    some v implies (v in BusinessRole and v.role = VENDOR)
}
check dom_referenceData_supplierIsVendor for 6

// Cross-tenant isolation holds for every resolved reference (regression guard for
// the kernel's CrossTenantIsolation) — UNSAT = holds.
assert dom_referenceData_tenantIsolation {
  all a: Scoped, id: a.refs | let b = resolve[id] |
    b in Scoped implies a.tenantId = b.tenantId
}
check dom_referenceData_tenantIsolation for 6

// Negative: no ItemSupply can resolve its vendor ref to a BusinessRole in a DIFFERENT
// tenant. Expect UNSAT — the kernel's CrossTenantIsolation makes it impossible.
run dom_referenceData_noCrossTenantSupplier {
  some s: ItemSupply, r: BusinessRole |
    s.supplier.vendorRef = r.eId and s.tenantId != r.tenantId
} for 6
