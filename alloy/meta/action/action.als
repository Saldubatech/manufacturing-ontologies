module meta/action/action

/*
 * Action — the execution of an activity, reified as an `Occurrence` in the Tick-ordered LOG
 * (DT-006, Layer 1 — structural ontology; dynamics deferred to Layer 2).
 *
 * READER'S MAP (one line each; the full anatomy, rationale, and decisions live in the workbook
 * design/meta/action — single source of truth; worked examples: ex15 guards/chaining, ex16 two
 * time models, ex17 snapshot chains):
 *  - STATE-AS-PROJECTION: no `World`, no domain `var` — state at tick t = a fold over
 *    `committedUpTo[t]`; a refused action contributes nothing (rollback is free).
 *  - `bindings: set univ` — the BINDING ENVIRONMENT: the quantifier prefix of the guarded formula
 *    ("∃ x such that guard(x) then effect(x)"); DERIVED per kind from named, TYPED binding fields.
 *  - Two guards bracket the Effect: `admission` reads the pre-projection (`committedBefore`),
 *    `commit` reads the post-projection (`committedUpTo`); both may read `by` (ABAC).
 *  - WITNESSING PATTERN: guards are made evaluable per kind by a fact tying the stored verdict to
 *    a predicate — `all a: K | a.admission = Accepted iff kAdmissible[a]`.
 *  - The EFFECT is not reified here (state-agnostic core); kinds that carry state snapshots open
 *    the OPTIONAL extension `meta/action/stateful` (`before`/`after`), where the Effect has a seat.
 */

open meta/occurrence/occurrence   // Occurrence (tick + effective `at`)
open meta/model_time/model_time   // Tick order vocabulary (precedes, notAfter)
open meta/principal/principal     // Principal (the "who")
open meta/action/outcome          // Decision, Accepted, Rejected, Reason

// ── anatomy ──────────────────────────────────────────────────────────────────────────────────────

/** Action — an executed activity, reified as an Occurrence (an entry in the log). */
abstract sig Action extends Occurrence {
  by:        one Principal,      // the acting principal (actor) — read by guards/Effect (ABAC); not a binding
  bindings:  set univ,           // the binding environment (quantifier prefix) — DERIVED from per-kind typed fields
  admission: one Decision,       // guard verdict on the pre-projection
  commit:    lone Decision       // guard verdict on the post-projection — present iff admitted
}

/** The commit guard is evaluated exactly when the action was admitted. */
fact CommitOnlyIfAdmitted { all a: Action | some a.commit iff a.admission = Accepted }

// ── the three outcomes (they partition Action) ───────────────────────────────────────────────────

/** committed — both gates accepted (only committed actions contribute to the state projection). */
pred committed[a: Action] { a.admission = Accepted and a.commit = Accepted }

/** refusedAtAdmission — the first gate refused; the action was never attempted against a result. */
pred refusedAtAdmission[a: Action] { a.admission in Rejected }

/** refusedAtCommit — admitted, but the result was refused by the second gate. */
pred refusedAtCommit[a: Action] { a.admission = Accepted and a.commit in Rejected }

/** refusalReasons — why a refused action did not take effect (from whichever guard rejected). */
fun refusalReasons[a: Action]: set Reason { a.admission.because + a.commit.because }

// ── projection domains — the log prefixes state is folded over ───────────────────────────────────

/** committedBefore — the committed log STRICTLY before `t`: the PRE-projection domain every
    admission guard reads ("the state just before me"). */
fun committedBefore[t: Tick]: set Action { { a: Action | committed[a] and precedes[a.tick, t] } }

/** committedUpTo — the committed log at-or-before `t` (inclusive): the POST-projection domain —
    an action's own contribution is visible at its own tick. A state query after a chain of actions
    is "filter this by kind/bindings, then fold" (keyed_sum for levels, LOCF for last-write-wins,
    existsAt-style for existence). */
fun committedUpTo[t: Tick]: set Action { { a: Action | committed[a] and notAfter[a.tick, t] } }
