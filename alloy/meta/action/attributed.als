module meta/action/attributed

/*
 * Attributed — the OPT-IN provenance/actor stamp on actions (DT-011 demotion, 2026-07-02): `by` was
 * part of the core anatomy, but no current theorem reads it, and carrying it by default put the
 * Principal family — and through it the whole identity KERNEL — into every action universe. Open this
 * where provenance or ABAC guards are actually wanted (the deferred WriteOff-authorization work is
 * the intended first consumer).
 *
 * A SUBSET sig (composes with `Timed` and `StatefulAction` — Alloy has single inheritance, so
 * independent opt-ins cannot be `extends` chains). A domain opts a KIND in with one fact
 * (`WriteOffOcc in Attributed`); guards then read `a.by` (ABAC).
 */

open meta/action/action           // Action
open meta/principal/principal     // Principal (the "who")

/** Attributed — an action carrying its acting principal (the actor; a parameter guards may read). */
sig Attributed in Action { by: one Principal }
