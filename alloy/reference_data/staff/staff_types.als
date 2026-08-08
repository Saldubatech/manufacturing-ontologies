module reference_data/staff/staff_types

// QUASI-STATIC SCOPE (the item / business_affiliate precedent): staff membership is
// SLOW-CHANGING relative to the model's trace window — a timescale scope decision, not an
// omission. The real system's horizon DOES include staff changes (hires, departures,
// renames), so the IMPLEMENTATION MUST provide pinning semantics (record rId / as-of
// reads) for every frozen holder of these entities. Consumer freeze laws to AUDIT if this
// module gains a log: procurement/order's assignee freeze (the sAssignee soft ref is
// frozen at Submit — verify the frozen holder still reads a pinned view). See
// modeling-conventions §7.

/*
 * STAFF — TYPES (DT-022 TQ-7(b), MP ruling 2026-08-07; DT-017 four-file architecture).
 * StaffMember represents a PERSON OR OTHER AGENT IN THE REAL WORLD (not to be confused
 * with system agents/principals — meta/principal is the occurrence-provenance identity;
 * a StaffMember is DOMAIN reference data: who can be assigned, named, held accountable
 * in business documents). For now an opaque identity asserting Entity individuality and
 * equality, plus a tenant-unique readable name; richer characterization (contact,
 * roles, systems identity linkage) comes later.
 */

open meta/profiles/baseline       // PROFILE (DT-012): structural — identity/refs/tenancy
open meta/kernel                  // Scoped, Entity, EntityId, resolve

/** StaffName — a staff member's readable name (opaque; content is runtime data). */
sig StaffName {}

/** StaffMember — a person or other real-world agent known to a tenant (assignable,
    accountable); reference data, NOT a system principal. */
sig StaffMember extends Scoped { name: one StaffName }

// No outgoing soft references (must be pinned, or `refs` is under-constrained).
fact StaffMemberRefs { all s: StaffMember | no s.dataRefs }

// Tight by default: no orphan names — StaffName is staff-local (single consumer).
fact NoOrphanStaffName { all n: StaffName | n in StaffMember.name }
