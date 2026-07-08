module reference_data/business_affiliate/business_affiliate_contracts

/*
 * BusinessAffiliate — CONTRACTS (DT-017): the published laws, curated and few. A STATIC
 * reference-data module (no log, no operations yet): one structural law.
 */

open reference_data/business_affiliate/business_affiliate_types

/** roleOwnership — every BusinessRole belongs to exactly one BusinessAffiliate and inherits
    its tenant. (The relational parentEId on the child is an impl artifact, not modeled.) */
pred roleOwnership {
  all r: BusinessRole | one b: BusinessAffiliate | r in b.roles
  all b: BusinessAffiliate, r: b.roles | r.tenantId = b.tenantId
}

/** guarantees — everything a consumer may assume of this module. */
pred guarantees { roleOwnership }
