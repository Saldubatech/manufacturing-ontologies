module meta/principal/principal

/*
 * Principal — the responsible identity ("who") on whose behalf an operation/occurrence is recorded (the
 * provenance author). A foundation for DT-006 (operations carry an author) and DT-010 (operation
 * confidence is attributed to the calling identity).
 *
 * NAMING: `Principal` (not `agent`). `agent` is reserved for the later "acting on behalf of" (delegation)
 * concept; an agent acts ON BEHALF OF a principal, so the two compose with no overlap.
 *
 * DECIDED (2026-06-30, from the current-system implementation):
 *   - **Fully an `Entity`** — identified by the kernel `eId` (unique via `EntityIdIsKey`) and soft-ref
 *     resolvable (`resolve[eId]`); this is how an `Occurrence` will reference its author.
 *   - **NOT `Scoped`** — a Principal is GLOBAL (no `tenantId`). Enforced STRUCTURALLY: `extends Entity`
 *     makes Principal a SIBLING of `Scoped`, so `Principal & Scoped` is empty by typing (stronger than a
 *     runtime fact). The Principal↔Tenant association is where the later `AgentFor` / agency concept takes
 *     on significance; it is deferred.
 *
 * DEFERRED (kept open to `extends`): `kind` (human vs system/automated — will matter for DT-010
 * confidence); any relationship to `reference_data` `BusinessAffiliate`.
 */

open meta/kernel   // Entity, EntityId, resolve

/** Name — an opaque, printable/readable identifier handle (a login/display), DISTINCT from the entity's
    `eId` (its opaque identity for soft references). Alloy has no strings; a distinct atom is a distinct
    canonical handle. */
sig Name {}

/** Principal — a responsible identity: fully an `Entity` (unique `eId`), NOT `Scoped` (global), with a
    unique readable handle. */
sig Principal extends Entity {
  name: one Name        // printable, readable handle
}

/** The readable handle identifies a principal for humans — no two principals share one. */
fact PrincipalNameUnique { all disj p, q: Principal | p.name != q.name }

/** A Principal carries no outgoing soft references yet (pin `dataRefs`, per the kernel convention). */
fact PrincipalNoDataRefs { no Principal.dataRefs }

/** Tight by default — every `Name` labels some principal. */
fact NoOrphanName { all n: Name | some name.n }

/** principalNamed — recover the principal bearing a given readable handle. */
fun principalNamed[n: Name]: lone Principal { name.n }
