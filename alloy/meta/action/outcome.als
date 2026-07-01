module meta/action/outcome

/*
 * The accept/reject vocabulary shared by an Action's two guards (admission + commit) — DT-006, Layer 1.
 * A guard yields a `Decision`: `Accepted`, or `Rejected` carrying the reason(s) it refused. Reasons are
 * opaque, reportable labels (Alloy has no strings; a distinct atom is a distinct canonical reason).
 *
 * Deliberately minimal. The action's overall RESULT (produced instances on success; reasons on refusal)
 * is DERIVED in `action.als` from the two decisions + the before/after states, not reified here.
 */

/** Reason — an opaque, reportable justification for a rejection (e.g. "Overdraw", "Locked"). */
sig Reason {}

/** Decision — a guard's verdict. */
abstract sig Decision {}

/** Accepted — the guard passed (one shared atom; carries no data). */
one sig Accepted extends Decision {}

/** Rejected — the guard refused, naming at least one reason. */
sig Rejected extends Decision { because: some Reason }
