module reference_data/shared/lifecycle

/*
 * Reference-data LIFECYCLE vocabulary (DT-023 R1, MP ruling 2026-08-10): the SIMPLE
 * log-carried lifecycle every proper reference-data module adopts —
 *
 *   [*] -> Live: Create ; Live -> Live: Update ; Live -> Retired: Delete ; Retired -> [*]
 *
 * Two statuses, terminal retirement (Reinstate is a deliberately free future seam — a new
 * kind on the log, no structural change). KINDS stay per-module (flat namespace; each
 * module declares its own Create/Update/Delete sigs on its own spine) — this file carries
 * only the shared STATUS vocabulary and the shared consumer-side refusal reason.
 *
 * SHARING SCOPE (DT-023 R2): item, business_affiliate, and staff MAY share this module.
 * `resources/processing_network` deliberately does NOT open it — Station/Loop are not
 * proper reference data and will acquire richer lifecycles; they repeat the pattern with
 * their own atoms rather than tie structurally to this vocabulary (repetition is the
 * accepted price of independence — MP, 2026-08-10).
 */

open meta/action/outcome   // Reason

/** RdStatus — a reference-data instance's lifecycle status: Live (usable as a reference
    target) or Retired (terminal; existing references are grandfathered per the DT-023
    matrix, new references refuse). */
abstract sig RdStatus {}
one sig RD_LIVE, RD_RETIRED extends RdStatus {}

/** RRetiredRef — the consumer-side refusal (DT-023 D2): an occurrence introducing a
    reference to a reference-data target whose current version at the occurrence's tick is
    Retired. One shared atom, same semantics in every consumer module (the RForeignRef
    naming precedent, hoisted here because the SAME rule guards every reference-data
    target). */
one sig RRetiredRef extends Reason {}
