module resources/processing_network/processing_network

open meta/profiles/baseline          // PROFILE (DT-012): structural — identity/refs/tenancy
open meta/kernel   // Scoped, EntityId

/*
 * Processing Network — STUB module [KC-MH-5 / KQ-S10]. Just enough Station/Loop to be soft-ref
 * targets for the Kanban Cards module. Source/Sink purity, per-loop roles, and the (directed,
 * possibly-cyclic / re-entrant) station network are DEFERRED. See the workbook
 * notebooks/domain-ontology/resources/processing_network/index.md.
 */

/** Station — a node in the processing network: consumes → transforms → produces (stub). */
sig Station extends Scoped {}

/** Loop — a configured DIRECTED route from a source station to a sink station (stub). */
sig Loop extends Scoped {
  source: one Station,
  sink:   one Station
}

fact LoopWellFormed {
  all l: Loop {
    l.source != l.sink                                              // distinct endpoints
    l.source.tenantId = l.tenantId and l.sink.tenantId = l.tenantId  // in-tenant (direct refs)
  }
}

// No soft references on the stubs (source/sink are direct, in-tenant relations).
fact ProcessingNetworkRefs {
  all s: Station | no s.dataRefs
  all l: Loop    | no l.dataRefs
}
