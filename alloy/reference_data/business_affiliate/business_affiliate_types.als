module reference_data/business_affiliate/business_affiliate_types

// QUASI-STATIC SCOPE (MP ruling 2026-07-08): this module is modeled IMMUTABLE because business
// affiliates are SLOW-CHANGING relative to the model's trace window — a timescale scope
// decision, not an omission. The real system's horizon (audit spans) DOES include their
// changes, so the IMPLEMENTATION MUST provide pinning semantics (record rId / as-of reads) for
// every frozen holder of these entities. Consumer freeze laws to AUDIT if this module gains a
// log: procurement/order `supplierBindingFrozen` (copy-covered today — verify the copy still
// covers every read). See modeling-conventions §7 (reference forms + the freeze obligation).

/*
 * BusinessAffiliate — TYPES (DT-017 four-file cut, 2026-07-08; content from the pre-cut
 * business_affiliate.als + business_role.als, unchanged): the entities, the role vocabulary,
 * the SupplierReference value, and the definitional ref facts. The ownership LAW lives in
 * business_affiliate_contracts.als; consumers' library files open THIS file only (laws arrive
 * via the root's mock/implementation choice).
 */

open meta/profiles/baseline       // PROFILE (DT-012): structural — identity/refs/tenancy
open meta/kernel                  // Scoped, Entity, EntityId, resolve

/** BusinessRoleType — the kind of role a business affiliate plays. */
enum BusinessRoleType { VENDOR, CUSTOMER, CARRIER, OPERATOR, OTHER }

/** BusinessRole — a role a BusinessAffiliate plays (e.g. VENDOR); a child entity of
    BusinessAffiliate, first-class as the target of SupplierReference. */
sig BusinessRole extends Scoped { role: one BusinessRoleType }

// No outgoing soft references (must be pinned, or `refs` is under-constrained).
fact BusinessRoleRefs { all r: BusinessRole | no r.dataRefs }

/** BusinessAffiliate — a legal entity participating in a tenant's transactions (as
    vendor, customer, carrier, …). */
sig BusinessAffiliate extends Scoped {
  roles: set BusinessRole          // parent → child aggregation (no backref)
}

// No outgoing soft references (must be pinned, or `refs` is under-constrained).
fact BusinessAffiliateRefs { all b: BusinessAffiliate | no b.dataRefs }

/** SupplierReference — a denormalized handle (soft EntityId refs) to a VENDOR BusinessRole
    and its affiliate, carried by item-side supply records (and, from DT-018, by the Order's
    SupplierBinding). */
sig SupplierReference {
  vendorRef:    lone EntityId,     // → BusinessRole(VENDOR)
  affiliateRef: lone EntityId      // → BusinessAffiliate
}
