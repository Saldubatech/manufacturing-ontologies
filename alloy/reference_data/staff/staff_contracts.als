module reference_data/staff/staff_contracts

/*
 * STAFF — CONTRACTS (DT-017): the published laws, curated and few. A STATIC
 * reference-data module (no log, no operations yet): one structural law.
 * Consistency class: ATOMIC (single-module structural invariant).
 */

open reference_data/staff/staff_types

/** staffNameUnique — a staff member's name is unique WITHIN its tenant (MP ruling,
    DT-022 TQ-7(b) follow-up, 2026-08-08); the same name may recur across tenants. */
pred staffNameUnique {
  all disj a, b: StaffMember | a.tenantId = b.tenantId implies a.name != b.name
}

/** guarantees — everything a consumer may assume of this module. */
pred guarantees { staffNameUnique }
