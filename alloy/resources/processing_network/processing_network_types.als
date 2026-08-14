module resources/processing_network/processing_network_types

// QUASI-STATIC SCOPE (MP ruling 2026-07-08): modeled IMMUTABLE — slow-changing relative to the
// model's trace window (a timescale scope decision). The IMPLEMENTATION MUST provide pinning
// semantics for frozen holders when station/loop data becomes editable. See
// modeling-conventions §7.

/*
 * PROCESSING NETWORK — TYPES (DT-017 four-file architecture; STUB module, cut 2026-07-06 for the
 * DT-016 demand build). Just enough Station/Loop to be soft-ref targets for the Kanban Cards and
 * Demand modules [KC-MH-5 / KQ-S10 / DT-016 R1]. Source/Sink purity, per-loop roles, and the
 * (directed, possibly-cyclic / re-entrant) station network are DEFERRED. See the workbook
 * design/resources/processing-network/.
 */

open meta/profiles/baseline          // PROFILE (DT-012): structural — identity/refs/tenancy
open meta/kernel                     // Scoped, EntityId
open meta/model_time/model_time      // Tick — the retirement LATCH's axis (DT-023 cut 7c)

// DT-023 cut 7c — the retirement LATCH (the D1(c) timeline-latch device): Station/Loop gain
// a universe-fixed retirement instant + liveness readings, with the module's OWN atoms — per
// the R2 structural-independence ruling ("Station/Loop are not proper reference-data
// entities... same lifecycle [shape] O.K., but not tied structurally"), this module does NOT
// open reference_data/shared/lifecycle: no RdStatus, no RRetiredRef, no log conversion. The
// latch makes retirement EXPRESSIBLE for future guards; consumer references (kanban loopRef,
// demand stationRef) stay soft and UNGATED — the D3 matrix rows are deferred to the Loop
// build-out (richer PN lifecycles supersede the latch there).

/** Station — a node in the processing network: consumes → transforms → produces (stub;
    identity + the retirement latch — DT-016 R1: the demand collation key's "for which
    consumption point"). */
sig Station extends Scoped { retiredAt: lone Tick }

/** Loop — a configured DIRECTED route from a source station to a sink station (stub;
    identity + the retirement latch). */
sig Loop extends Scoped {
  source: one Station,
  sink:   one Station,
  retiredAt: lone Tick
}

/** stationLiveAt / loopLiveAt — the liveness readings over the latch: live at `t` iff not
    yet retired (the boundary is EXCLUSIVE — retired FROM `retiredAt` on). */
pred stationLiveAt[s: Station, t: Tick] { no s.retiredAt or precedes[t, s.retiredAt] }
pred loopLiveAt[l: Loop, t: Tick]       { no l.retiredAt or precedes[t, l.retiredAt] }

// ── definitional facts (shape, not promises) ────────────────────────────────────────────────────
// No soft references on the stubs (source/sink are direct, in-tenant relations).
fact ProcessingNetworkRefs {
  all s: Station | no s.dataRefs
  all l: Loop    | no l.dataRefs
}
