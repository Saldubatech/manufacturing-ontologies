module reference_data/business_role

open meta/kernel

enum BusinessRoleType { VENDOR, CUSTOMER, CARRIER, OPERATOR, OTHER }

// A role a business affiliate plays. Child entity of BusinessAffiliate (owned via
// BusinessAffiliate.roles; ownership + scope facts live there). First-class (not a
// value) because it is the target of SupplierReference (the VENDOR role).
sig BusinessRole extends Scoped { role: one BusinessRoleType }

// No outgoing soft references (must be pinned, or `refs` is under-constrained).
fact BusinessRoleRefs { all r: BusinessRole | no r.dataRefs }
