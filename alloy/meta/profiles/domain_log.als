module meta/profiles/domain_log

/*
 * P1 — DOMAIN LOG: the DEFAULT profile for operational domain modules (DT-012): subjects with
 * operations, refusals, and history. Bundles the log anatomy (StatefulAction: snapshots, guards,
 * committed prefixes — via meta/action/stateful) with the quantitative premises domain arithmetic
 * needs (the abelian GROUP + the posited order). Opening this profile ENFORCES the premises in the
 * whole cone (that is the point — adoption is the opt-in); tick-only time (wall-clock is P2).
 *
 * The domain still supplies, per the kit: a Snapshot record (+ extensionality + intra-state facts),
 * kinds with typed bindings, UNCONDITIONAL chaining, witnessed guards (coarse by default), and the
 * stateAt/liveAt projections. Template: ex18; exemplar: resources/inventory_item.
 */

open meta/profiles/baseline                  // P0 (kernel)
open meta/action/stateful                    // Action + Stateful (pre/post) + occurrence/model_time/outcome
open meta/keyed_value_algebra/keyed_order    // lte/classify/semanticEq (+ keyed_monoid: add/negate/zero)

/** P_DomainLog — the marker: this universe models under the domain-log profile. */
one sig P_DomainLog extends Profile {}

// Adoption = opt-in: the additive, ordered quantity algebra is IN FORCE for the whole cone.
// (Multiplication/`ringAxioms` is deliberately NOT here — that is conversion work, à la carte.)
fact DomainLogPremises { groupAxioms and orderAxioms }
