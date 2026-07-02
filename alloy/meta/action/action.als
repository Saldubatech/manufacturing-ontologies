module meta/action/action

/*
 * Action — the execution of an activity that effects change in the System, reified as an `Occurrence`
 * (DT-006, Layer 1 — the STRUCTURAL ontology; dynamics deferred).
 *
 * STATE-AS-PROJECTION (2026-06-30): there is NO reified `World` and NO domain `var` trace. The canonical
 * artifact is the reified, `Tick`-ordered **log** of actions; the System **state is a PROJECTION (fold)
 * over that log** — the accumulation of committed effects up to a tick. So this framework reifies only the
 * LOG + the action anatomy (who / bindings / the two guard verdicts / outcome); it is deliberately
 * STATE-AGNOSTIC. How state is projected is domain-specific — additive levels via `keyed_sum[Occurrence]`,
 * or last-write-wins attributes via LOCF (cf. `meta/measurement.valueAt`). See design/meta/action, and the
 * test root for a worked existence projection.
 *
 * BINDINGS (2026-07-01, DT-006 decision): an action's `bindings` is its BINDING ENVIRONMENT — the
 * quantifier prefix of the guarded formula ("∃/∀ x, y such that guard(x,y) then effect(x,y)"). A binding
 * may be an Entity, a Value, or any other model element, hence `set univ` (the former `sig Instance` was
 * a misencoding: a fresh top-level sig is disjoint from every domain type, so nothing real could be
 * bound). `bindings` is DERIVED, never primary: each concrete kind declares named, TYPED binding fields
 * (`target: one InventoryItem`, `amount: one Quantity`) — those are the quantifier variables — and pins
 * `bindings` to their union in its appended fact. By convention bindings exclude the action machinery's
 * own atoms (Ticks, Decisions, Reasons); this is a doc rule, not a fact.
 *
 * Guards are made EVALUABLE per kind by the witnessing pattern (Alloy cannot store a predicate as data):
 *   fact KAdmission { all a: K | a.admission = Accepted iff kAdmissible[a] }
 * where `kAdmissible` ranges over the bindings and the pre-projection (mirrors DT-003's `firedInto`).
 *
 * Anatomy: performed `by` a Principal (the acting ACTOR — a parameter, never a binding; read by
 * guards/Effect — ABAC); an `admission` guard reads the pre-projection, a `commit` guard the
 * post-projection; the action `committed` iff both Accept. A refused action contributes NOTHING to the
 * projection (rollback is automatic — the projection counts only committed effects).
 */

open meta/occurrence/occurrence   // Occurrence (tick + effective `at`)
open meta/model_time/model_time   // Tick order vocabulary (precedes, notAfter) — used by committedUpTo
open meta/principal/principal     // Principal (the "who")
open meta/action/outcome          // Decision, Accepted, Rejected, Reason

/** Action — an executed activity, reified as an Occurrence (an entry in the log). */
abstract sig Action extends Occurrence {
  by:        one Principal,      // the acting principal (actor) — read by guards/Effect (ABAC); not a binding
  bindings:  set univ,           // the binding environment (quantifier prefix) — DERIVED from per-kind typed fields
  admission: one Decision,       // guard verdict on the pre-projection
  commit:    lone Decision       // guard verdict on the post-projection — present iff admitted
}

/** The commit guard is evaluated exactly when the action was admitted. */
fact CommitOnlyIfAdmitted { all a: Action | some a.commit iff a.admission = Accepted }

/** committed — both gates accepted (only committed actions contribute to the state projection). */
pred committed[a: Action] { a.admission = Accepted and a.commit = Accepted }

/** blockedBy — the reasons a refused action did not take effect (from whichever guard rejected). */
fun blockedBy[a: Action]: set Reason { a.admission.because + a.commit.because }

/** committedUpTo — the committed prefix of the log at tick `t`: the domain of every state projection.
    A state query after a chain of actions is "filter this by kind/bindings, then fold"
    (keyed_sum for levels, LOCF for last-write-wins, existsAt-style for existence). */
fun committedUpTo[t: Tick]: set Action { { a: Action | committed[a] and notAfter[a.tick, t] } }
