module meta/action/tests/action

open meta/action/action
open meta/model_time/model_time   // precedes, notAfter (over Tick) — for the projection

/*
 * v1 (state-as-projection). Two parts: the state-agnostic anatomy laws, and a worked demonstration that
 * System state is a PROJECTION over the reified log — here, instance existence reconstructed from the
 * committed Create/Delete log, with NO `World` sig. `Action` is abstract, so concrete kinds are used.
 */

/** Op — a concrete action with a free outcome, to exercise the anatomy. */
sig Op extends Action {}

// ── anatomy (state-agnostic) ─────────────────────────────────────────────────────────────────────
// A committed action exists.
run unit_action_committed { some a: Op | committed[a] } for 4 expect 1

// A commit rejection: admitted, but the commit gate refuses.
run unit_action_commitRejected { some a: Op | a.admission = Accepted and a.commit in Rejected } for 4 expect 1

// Every refusal carries at least one reason.
assert unit_action_refusalHasReason { all a: Action | not committed[a] implies some blockedBy[a] }
check unit_action_refusalHasReason for 5 expect 0

// A success carries no reasons.
assert unit_action_successNoReason { all a: Action | committed[a] implies no blockedBy[a] }
check unit_action_successNoReason for 5 expect 0

// ── state-as-projection: existence folded from the committed Create/Delete log (no `World`) ─────────
/** Create — brings a new instance into existence; context = the created instance (an output binding). */
sig Create extends Action { made: one Instance } { context = made }
/** Delete — removes an existing instance; context = the deleted instance (an input binding). */
sig Delete extends Action { gone: one Instance } { context = gone }

/** existsAt — the existence PROJECTION: `i` is present at tick `t` iff a COMMITTED Create of `i` sits
    at/before `t` with no COMMITTED Delete of `i` strictly between that create and `t`. State is a fold of
    the log; refused actions (not `committed`) contribute nothing. */
pred existsAt[i: Instance, t: Tick] {
  some c: Create | committed[c] and c.made = i and notAfter[c.tick, t] and
    (no d: Delete | committed[d] and d.gone = i and precedes[c.tick, d.tick] and notAfter[d.tick, t])
}

// A committed Create projects its instance into existence (state reflects committed effects).
run unit_action_createProjects {
  some c: Create | committed[c] and existsAt[c.made, c.tick]
} for 4 expect 1

// A REFUSED Create contributes nothing — its instance is absent from the projection at every tick.
run unit_action_refusedCreateNoProject {
  some c: Create | not committed[c] and (all t: Tick | not existsAt[c.made, t])
} for 4 expect 1

// A committed Delete after a committed Create removes the instance from the projection at the delete tick.
run unit_action_deleteProjects {
  some c: Create, d: Delete |
    committed[c] and committed[d] and c.made = d.gone
    and precedes[c.tick, d.tick] and not existsAt[c.made, d.tick]
} for 5 expect 1
