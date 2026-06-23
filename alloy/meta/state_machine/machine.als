module meta/state_machine/machine

/*
 * Generic finite-state-machine framework, reifying common-module's StateEngine
 * (cards.arda.common.lib.service.stateengine) as data, so its guarantees become
 * once-stated, machine-generic theorems instead of per-entity transition tables.
 * See DT-003.
 *
 * A concrete machine is configured by: extending State/Signal with enum-like
 * one-sigs; minting a family of Transition one-sigs; and pinning one StateMachine
 * atom's states/signals/start/transitions via facts. Well-formedness and
 * determinism hold for ALL machines (facts). Reachability and live-signals are
 * checkable PROPERTIES, not facts — a real machine may violate them, and that is
 * exactly how the model surfaces gaps (unreachable states, dead signals).
 */

/** State — a state of some state machine; a concrete machine's state enum extends it. */
abstract sig State  {}
/** Signal — an event that drives a transition; a concrete machine's signal enum extends it. */
abstract sig Signal {}

/** Guard — an opaque discriminator distinguishing transitions that share a (state, signal);
    the structural face of "exactly one applicable transition" (reifies a StateEngine guard). */
sig Guard {}

/** Transition — a reified edge: from a set of source states (the resolved StatePattern;
    ANY = all states), on a signal, to a target state (absent = Same/self-loop), optionally guarded. */
sig Transition {
  from:  some State,
  on:    one Signal,
  to:    lone State,
  guard: lone Guard
}

/** StateMachine — a reified finite-state machine: its states, signals, start state, and transitions. */
sig StateMachine {
  states:      some State,
  signals:     some Signal,
  start:       one State,
  transitions: set Transition
}

// --- generic well-formedness (FACTS — true of every machine) ----------------
fact MachineWellFormed {
  all m: StateMachine {
    m.start in m.states
    all t: m.transitions {
      t.from in m.states
      t.on   in m.signals
      t.to   in m.states          // `to` lone: absent (Same) trivially holds
    }
  }
}

// Determinism modulo guard: per (state, signal), distinct applicable transitions
// must differ in guard (mirrors transitionFor requiring exactly one to pass).
fact Deterministic {
  all m: StateMachine, s: State, sg: Signal |
    all disj a, b: m.transitions |
      (s in a.from and a.on = sg and s in b.from and b.on = sg) implies a.guard != b.guard
}

// Tight by default (§6): no orphan reified atoms — every State/Signal belongs to a
// machine, every Transition is owned by a machine, every Guard is used.
fact NoOrphanState      { all s: State      | some m: StateMachine | s in m.states }
fact NoOrphanSignal     { all g: Signal     | some m: StateMachine | g in m.signals }
fact NoOrphanTransition { all t: Transition | some m: StateMachine | t in m.transitions }
fact NoOrphanGuard      { all g: Guard      | g in Transition.guard }

// --- generic structure helpers ----------------------------------------------
// One-signal successor relation: Explicit → t.to; Same → stay at the source.
fun succ[m: StateMachine]: State -> State {
  { s, d: m.states |
      some t: m.transitions | s in t.from and (d = t.to or (no t.to and d = s)) }
}
fun reachable[m: StateMachine]: set State { m.start.*(succ[m]) }

// --- generic checkable properties (NOT facts: a buggy machine may fail them) --
pred allStatesReachable[m: StateMachine] { m.states in reachable[m] }
pred liveSignals[m: StateMachine]        { m.signals in m.transitions.on }

// Snapshot consistency (DT-001.02 (b), reified): a host whose last signal in this
// machine was `sig` and whose current state is `cur` is consistent iff some
// transition on `sig` lands at `cur` (Explicit) or holds `cur` (Same). Hosts invoke
// this in their OWN fact, binding their state / last-signal fields.
pred firedInto[m: StateMachine, cur: lone State, sg: Signal] {
  some t: m.transitions | t.on = sg and (cur = t.to or (no t.to and cur in t.from))
}
