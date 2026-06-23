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
// `dataRefs` is the set of OUTGOING soft references the entity's module declares (the
// data references, excluding the scope ref). Each concrete entity's module pins it
// (one fact; `no x.dataRefs` when it holds none), since Alloy has no field
// reflection. The COMPLETE reference set is the derived `refs` (below).
abstract sig Entity {
  eId:      one EntityId,
  dataRefs: set EntityId
}
fact EntityIdIsKey { all disj a, b: Entity | a.eId != b.eId }

// Tenant-scoped entity. `tenantId` is a SOFT reference (an EntityId, not a Tenant
// sig) — keeps meta/kernel free of any domain dependency. The Tenant entity lives
// in the system domain (not yet modeled); "tenantId resolves to a Tenant" is a
// check for a root that opens both.
abstract sig Scoped extends Entity { tenantId: one EntityId }

// The COMPLETE set of an entity's outgoing soft references: the module-declared
// `dataRefs` PLUS, for a Scoped entity, its scope reference (`tenantId`).
// `this.tenantId` is empty for non-Scoped entities, so this holds for any Entity.
// Generic cross-reference rules quantify over `refs`.
fun Entity.refs: set EntityId { this.dataRefs + this.tenantId }

// Cross-tenant isolation — over the complete `refs` set, restricted to tenant-bearing
// entities: if a Scoped entity refers to another Scoped entity that resolves in
// scope, they share a tenant. Refs to non-Scoped/global entities (incl. the scope
// ref's Tenant), or unresolved refs, are exempt via the `b in Scoped` guard.
fact CrossTenantIsolation {
  all a: Scoped, id: a.refs |
    let b = resolve[id] | b in Scoped implies a.tenantId = b.tenantId
}

// Tight by default: no orphan identities — every EntityId is either some entity's
// own identity or is referenced by some entity. (Relax explicitly to model a
// minted-but-not-yet-used id.) See modeling-conventions §6.
fact NoOrphanEntityId { all id: EntityId | id in Entity.eId + Entity.refs }

// Resolve a soft reference within the current scope. `lone`: 0 (dangling /
// not-loaded / cross-Universe — the 'soft' case) or 1 (key ⇒ never more).
fun resolve[id: EntityId]: lone Entity { eId.id }
