module reference_data/staff/tests/staff

/*
 * STAFF — module suite (DT-022 TQ-7(b), cut 6). Static degenerate module: joint
 * satisfiability + the uniqueness law + the cross-tenant boundary witness.
 */

open reference_data/staff/staff_implementation

/** unit_stf_loads — the module is jointly satisfiable with two staff members. */
pred unit_stf_loads { #StaffMember >= 2 }
run unit_stf_loads for 4 but 6 EntityId expect 1

/** unit_stf_nameUniqueInTenant — no two same-tenant members share a name (the law,
    restated as an assertion over the implementation). */
assert unit_stf_nameUniqueInTenant {
  all disj a, b: StaffMember | a.tenantId = b.tenantId implies a.name != b.name
}
check unit_stf_nameUniqueInTenant for 5 but 8 EntityId expect 0

/** unit_stf_sameNameAcrossTenants — BOUNDARY: the SAME name legally recurs in two
    different tenants (uniqueness is tenant-scoped, not global). */
pred unit_stf_sameNameAcrossTenants {
  some disj a, b: StaffMember | a.tenantId != b.tenantId and a.name = b.name
}
run unit_stf_sameNameAcrossTenants for 4 but 6 EntityId expect 1
