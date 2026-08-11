module reference_data/shared/tests/shared

open meta/kernel
open reference_data/item/item_implementation
open reference_data/business_affiliate/business_affiliate_implementation


// reference_data/shared — the DOMAIN-level shared module (the meta-equivalent at domain scope): holds
// cross-module verifications (and any domain-shared super-classes, when they arise) that belong to no
// single module. Here: the reference chain Item → ItemSupply → SupplierReference → BusinessRole(VENDOR)
// → BusinessAffiliate, which spans the item and business_affiliate modules.

// A fully-linked single-tenant instance exists — the whole chain is satisfiable (not over-constrained).
pred coherent {
  some i: Item, s: ItemSupply, ba: BusinessAffiliate, r: BusinessRole |
    s in itemSuppliesOf[i]   // version-carried since DT-023 cut 7a (the supply rides i's log)
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

// ── the named happy-path witnesses (unwitnessed-scenarios follow-up, 2026-07-08) ────────────────
// Previously covered only implicitly by the joint-SAT load; named so the shapes cannot silently
// die (the vacuous-witness lesson: a witness must EXCLUDE the degenerate satisfactions).

// The CLEAN resolution read: a fully-LINKED supplier reference — BOTH handles present, resolving,
// mutually consistent (the vendor role is owned by the referenced affiliate), same tenant — and NO
// dangling handle anywhere in the instance (the negative conjunct).
run unit_shared_cleanResolution {
  some s: ItemSupply, r: BusinessRole, ba: BusinessAffiliate | {
    resolve[s.supplier.vendorRef] = r
    resolve[s.supplier.affiliateRef] = ba
    r in ba.roles and r.role = VENDOR
    s.tenantId = ba.tenantId
  }
  no sr: SupplierReference {
    (some sr.vendorRef and no resolve[sr.vendorRef]) or
    (some sr.affiliateRef and no resolve[sr.affiliateRef])
  }
} for 6 expect 1

// The linked-VENDOR selection is PRECISE, not incidental: the referenced affiliate bears MORE THAN
// ONE role, and the reference resolves to exactly its VENDOR one.
run unit_shared_linkedVendorPrecise {
  some s: ItemSupply, ba: BusinessAffiliate, disj r1, r2: BusinessRole | {
    r1 in ba.roles and r2 in ba.roles and r1.role = VENDOR and r2.role != VENDOR
    resolve[s.supplier.vendorRef] = r1
    resolve[s.supplier.affiliateRef] = ba
  }
} for 6 expect 1
