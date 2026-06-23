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
// `refs` is the set of OUTGOING soft references this entity holds — it belongs at the
// Entity level (any entity may hold references, scoped or not) and is the hook for
// generic cross-reference rules. Alloy has no field reflection, so each concrete
// entity's module pins its `refs` (one fact; `no x.refs` when it holds none) or the
// field is left under-constrained.
abstract sig Entity {
  eId:  one EntityId,
  refs: set EntityId
}
fact EntityIdIsKey { all disj a, b: Entity | a.eId != b.eId }

// Tenant-scoped entity. `tenantId` is a SOFT reference (an EntityId, not a Tenant
// sig) — keeps meta/kernel free of any domain dependency. The Tenant entity lives
// in the system domain (not yet modeled); "tenantId resolves to a Tenant" is a
// check for a root that opens both. (`refs` is inherited from Entity.)
abstract sig Scoped extends Entity { tenantId: one EntityId }

// Cross-tenant isolation — one rule over `Entity.refs`, but restricted to
// tenant-bearing entities: if a Scoped entity refers to another Scoped entity that
// resolves in scope, they share a tenant. Refs to non-Scoped/global entities, or
// unresolved refs, are exempt via the `b in Scoped` guard.
fact CrossTenantIsolation {
  all a: Scoped, id: a.refs |
    let b = resolve[id] | b in Scoped implies a.tenantId = b.tenantId
}

// Resolve a soft reference within the current scope. `lone`: 0 (dangling /
// not-loaded / cross-Universe — the 'soft' case) or 1 (key ⇒ never more).
fun resolve[id: EntityId]: lone Entity { eId.id }
