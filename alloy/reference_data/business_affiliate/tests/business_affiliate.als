module reference_data/business_affiliate/tests/business_affiliate

open meta/kernel
open reference_data/business_affiliate/business_affiliate
open reference_data/business_affiliate/business_role

// Business-affiliate-module verification: BusinessAffiliate + child BusinessRole. The cross-module
// supply→supplier chain is verified from the item side (reference_data/item/tests).

// A BusinessAffiliate bearing a VENDOR role exists — BA + its child roles cohere.
pred coherent {
  some ba: BusinessAffiliate, r: BusinessRole | r in ba.roles and r.role = VENDOR
}
run unit_ba_coherent { coherent } for 6 expect 1

// A single affiliate can bear several roles of different types (e.g. VENDOR and CUSTOMER).
run unit_ba_multiRole {
  some ba: BusinessAffiliate, disj r1, r2: BusinessRole |
    r1 in ba.roles and r2 in ba.roles and r1.role != r2.role
} for 6 expect 1

// BusinessRole child ownership is exclusive — UNSAT = holds.
check unit_ba_roleOwnership {
  no r: BusinessRole | some disj b1, b2: BusinessAffiliate | r in b1.roles and r in b2.roles
} for 6 expect 0
