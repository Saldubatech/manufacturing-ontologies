module reference_data/business_affiliate/business_role

open meta/kernel

/** BusinessRoleType — the kind of role a business affiliate plays. */
enum BusinessRoleType { VENDOR, CUSTOMER, CARRIER, OPERATOR, OTHER }

/** BusinessRole — a role a BusinessAffiliate plays (e.g. VENDOR); a child entity of
    BusinessAffiliate, first-class as the target of SupplierReference. */
sig BusinessRole extends Scoped { role: one BusinessRoleType }

// No outgoing soft references (must be pinned, or `refs` is under-constrained).
fact BusinessRoleRefs { all r: BusinessRole | no r.dataRefs }
