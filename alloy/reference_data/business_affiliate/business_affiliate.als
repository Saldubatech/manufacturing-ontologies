module reference_data/business_affiliate/business_affiliate

open meta/profiles/baseline          // PROFILE (DT-012): structural — identity/refs/tenancy
open meta/kernel
open reference_data/business_affiliate/business_role

/** BusinessAffiliate — a legal entity participating in a tenant's transactions (as
    vendor, customer, carrier, …). */
sig BusinessAffiliate extends Scoped {
  roles: set BusinessRole          // parent → child aggregation (no backref)
}

// Every BusinessRole belongs to exactly one BusinessAffiliate and inherits its
// tenant. (The relational parentEId on the child is an impl artifact, not modeled.)
fact BusinessRoleOwnership {
  all r: BusinessRole | one b: BusinessAffiliate | r in b.roles
  all b: BusinessAffiliate, r: b.roles | r.tenantId = b.tenantId
}

// No outgoing soft references (must be pinned, or `refs` is under-constrained).
fact BusinessAffiliateRefs { all b: BusinessAffiliate | no b.dataRefs }

/** SupplierReference — a denormalized handle (soft EntityId refs) to a VENDOR BusinessRole
    and its affiliate, carried by item-side supply records. */
sig SupplierReference {
  vendorRef:    lone EntityId,     // → BusinessRole(VENDOR)
  affiliateRef: lone EntityId      // → BusinessAffiliate
}
