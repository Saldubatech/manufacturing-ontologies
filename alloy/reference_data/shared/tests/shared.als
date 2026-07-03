module reference_data/shared/tests/shared

open meta/kernel
open reference_data/item/item_implementation
open reference_data/business_affiliate/business_affiliate
open reference_data/business_affiliate/business_role

// reference_data/shared — the DOMAIN-level shared module (the meta-equivalent at domain scope): holds
// cross-module verifications (and any domain-shared super-classes, when they arise) that belong to no
// single module. Here: the reference chain Item → ItemSupply → SupplierReference → BusinessRole(VENDOR)
// → BusinessAffiliate, which spans the item and business_affiliate modules.

// A fully-linked single-tenant instance exists — the whole chain is satisfiable (not over-constrained).
pred coherent {
  some i: Item, s: ItemSupply, ba: BusinessAffiliate, r: BusinessRole |
    s in i.supplies
    and r in ba.roles
    and r.role = VENDOR
    and s.supplier.vendorRef = r.eId
    and i.tenantId = ba.tenantId
}
run unit_shared_coherent { coherent } for 6 expect 1

// A resolved supplier reference is always a VENDOR role — UNSAT = holds.
check unit_shared_supplierIsVendor {
  all s: ItemSupply | let v = resolve[s.supplier.vendorRef] |
    some v implies (v in BusinessRole and v.role = VENDOR)
} for 6 expect 0

// Cross-tenant isolation over every resolved reference (kernel CrossTenantIsolation regression) — UNSAT.
// `some b` guard: an EMPTY resolve satisfies `b in Scoped` (subset), so the unguarded form is
// falsified by any dangling ref — same empty-set bug as the 2026-07-01 kernel fix.
check unit_shared_tenantIsolation {
  all a: Scoped, id: a.refs | let b = resolve[id] |
    (some b and b in Scoped) implies a.tenantId = b.tenantId
} for 6 expect 0

// Negative: no ItemSupply resolves its vendor ref to a BusinessRole in a different tenant — UNSAT.
run unit_shared_noCrossTenantSupplier {
  some s: ItemSupply, r: BusinessRole |
    s.supplier.vendorRef = r.eId and s.tenantId != r.tenantId
} for 6 expect 0
