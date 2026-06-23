module meta/kernel

/*
 * Modeling kernel: identity, the Entity bound, tenant scoping, soft-reference
 * resolution. Domain payloads extend Entity (or Scoped). Timeless — the temporal
 * axis is the opt-in meta/bitemporal layer (DT-001.03). See modeling-conventions.
 */

// Opaque, globally-unique identity. Alloy atoms are inherently distinct and `=` is
// identity equality, so each EntityId atom IS a unique identity.
sig EntityId {}

// Identity-bearing thing. `eId` is a primary key (injective — EntityIdIsKey).
abstract sig Entity { eId: one EntityId }
fact EntityIdIsKey { all disj a, b: Entity | a.eId != b.eId }

// Tenant-scoped entity. `tenantId` is a SOFT reference (an EntityId, not a Tenant
// sig) — keeps meta/kernel free of any domain dependency. The Tenant entity lives
// in the system domain (not yet modeled); "tenantId resolves to a Tenant" is a
// check for a root that opens both.
abstract sig Scoped extends Entity { tenantId: one EntityId }

// Resolve a soft reference within the current scope. `lone`: 0 (dangling /
// not-loaded / cross-Universe — the 'soft' case) or 1 (key ⇒ never more).
fun resolve[id: EntityId]: lone Entity { eId.id }
