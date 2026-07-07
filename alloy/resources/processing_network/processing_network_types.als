module resources/processing_network/processing_network_types

/*
 * PROCESSING NETWORK — TYPES (DT-017 four-file architecture; STUB module, cut 2026-07-06 for the
 * DT-016 demand build). Just enough Station/Loop to be soft-ref targets for the Kanban Cards and
 * Demand modules [KC-MH-5 / KQ-S10 / DT-016 R1]. Source/Sink purity, per-loop roles, and the
 * (directed, possibly-cyclic / re-entrant) station network are DEFERRED. See the workbook
 * design/resources/processing-network/.
 */

open meta/profiles/baseline          // PROFILE (DT-012): structural — identity/refs/tenancy
open meta/kernel                     // Scoped, EntityId

/** Station — a node in the processing network: consumes → transforms → produces (stub;
    identity-only — DT-016 R1: the demand collation key's "for which consumption point"). */
sig Station extends Scoped {}

/** Loop — a configured DIRECTED route from a source station to a sink station (stub). */
sig Loop extends Scoped {
  source: one Station,
  sink:   one Station
}

// ── definitional facts (shape, not promises) ────────────────────────────────────────────────────
// No soft references on the stubs (source/sink are direct, in-tenant relations).
fact ProcessingNetworkRefs {
  all s: Station | no s.dataRefs
  all l: Loop    | no l.dataRefs
}
