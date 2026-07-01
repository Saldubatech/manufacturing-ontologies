module meta/action/action

/*
 * Action — the execution of an activity that effects change in the System, reified as an `Occurrence`
 * (DT-006, Layer 1 — the STRUCTURAL ontology; dynamics deferred).
 *
 * STATE-AS-PROJECTION (2026-06-30): there is NO reified `World` and NO domain `var` trace. The canonical
 * artifact is the reified, `Tick`-ordered **log** of actions; the System **state is a PROJECTION (fold)
 * over that log** — the accumulation of committed effects up to a tick. So this framework reifies only the
 * LOG + the action anatomy (who / context / the two guard verdicts / outcome); it is deliberately
 * STATE-AGNOSTIC. How state is projected is domain-specific — additive levels via `keyed_sum[Occurrence]`,
 * or last-write-wins attributes via LOCF (cf. `meta/measurement.valueAt`). See design/meta/action, and the
 * test root for a worked existence projection.
 *
 * Anatomy: performed `by` a Principal (the acting ACTOR — context, not System state) over a `context` of
 * bound instances; an `admission` guard reads the pre-projection, a `commit` guard the post-projection;
 * the action `committed` iff both Accept. A refused action contributes NOTHING to the projection (rollback
 * is automatic — the projection counts only committed effects). Guards/Effect are parameterized by `by`
 * (ABAC / principal-dependent).
 */

open meta/occurrence/occurrence   // Occurrence (tick + effective `at`); re-exports model_time (precedes, notAfter)
open meta/principal/principal     // Principal (the "who")
open meta/action/outcome          // Decision, Accepted, Rejected, Reason

/** Instance — an element of the System (a domain object an action inspects / mutates / creates). */
sig Instance {}

/** Action — an executed activity, reified as an Occurrence (an entry in the log). */
abstract sig Action extends Occurrence {
  by:        one Principal,      // the acting principal (actor) — read by guards/Effect (ABAC); not state
  context:   set Instance,       // the bound instances it inspects / mutates / creates (its footprint)
  admission: one Decision,       // guard verdict on the pre-projection
  commit:    lone Decision       // guard verdict on the post-projection — present iff admitted
}

/** The commit guard is evaluated exactly when the action was admitted. */
fact CommitOnlyIfAdmitted { all a: Action | some a.commit iff a.admission = Accepted }

/** committed — both gates accepted (only committed actions contribute to the state projection). */
pred committed[a: Action] { a.admission = Accepted and a.commit = Accepted }

/** blockedBy — the reasons a refused action did not take effect (from whichever guard rejected). */
fun blockedBy[a: Action]: set Reason { a.admission.because + a.commit.because }
