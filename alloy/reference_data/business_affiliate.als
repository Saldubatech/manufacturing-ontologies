module reference_data/business_affiliate

open meta/kernel
open reference_data/business_role

// A legal entity participating in a tenant's transactions.
sig BusinessAffiliate extends Scoped {
  roles: set BusinessRole          // parent → child aggregation (no backref)
}

// Every BusinessRole belongs to exactly one BusinessAffiliate and inherits its
// tenant. (The relational parentEId on the child is an impl artifact, not modeled.)
fact BusinessRoleOwnership {
  all r: BusinessRole | one b: BusinessAffiliate | r in b.roles
  all b: BusinessAffiliate, r: b.roles | r.tenantId = b.tenantId
}

// Denormalized cross-module handle to a VENDOR BusinessRole (and its affiliate),
// carried by item-side supply records. Soft references (EntityId) — `lone` because
// a handle may be unresolved/denormalized across Universes.
sig SupplierReference {
  vendorRef:    lone EntityId,     // → BusinessRole(VENDOR)
  affiliateRef: lone EntityId      // → BusinessAffiliate
}
