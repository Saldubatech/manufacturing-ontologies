module meta/examples/ex16_two_time_models

/*
 * PATTERN:  The SAME changing object modeled under both time representations — (1) Alloy 6 `var`/LTL:
 *           time as SEMANTICS, an instance is a trace, state is held and stepped; (2) the reified log
 *           + projection (DT-001.03/DT-006): time as DATA, an instance encodes a whole history, state
 *           is a fold over the tick-ordered event atoms. The punchline is a machine-checked AGREEMENT
 *           THEOREM: replaying the log through the `var` transition system yields, at every step,
 *           exactly the projection's state. This is the reconciliation obligation the two-view
 *           architecture carries (cf. ex14's frameworkMatchesEventSource).
 * UML:      state machine (transitions on a held object) vs event store + derived view.
 * FP:       State-monad step function vs foldl over an event list — and a proof they commute.
 * USE WHEN:  choosing a time representation: transition-legality questions (guards, lifecycle order,
 *           liveness) want `var`/LTL; history-as-data questions (as-of queries, cross-time joins,
 *           counting, provenance, backdating) want the reified log. When both are needed (the live
 *           model!), state the agreement as a check.
 * AVOID:     smuggling history into `var` via auxiliary variables (you are rebuilding the log without
 *           its benefits), and cross-time arithmetic in LTL (it has no names for moments and cannot
 *           count). Also: a bare (un-`always`ed) invariant over `var` fields — initial-state-only,
 *           modeling-conventions §3.2.
 * SEE ALSO:  the methodology narrative behind this example: workbook `modeling/two-time-models.md`
 *           (condition-by-condition comparison, trade-off table, why the live model runs both).
 *           Also meta/model_time; meta/action (state-as-projection, committedUpTo); ex14
 *           (event-sourced LEVEL); ex09 (machines); DT-001.03 (two clocks); DT-006 open #2.
 *
 * Neutral cast: a hotel's stack of ROOM-SERVICE TRAYS at the service station — trays are stacked
 * (push) and taken from the top (pop). LIFO by physics. The tray-stack is the "unbounded stack" toy;
 * note NEITHER model is truly unbounded: the trace model bounds time by `steps`, the log model by the
 * `Tick` scope — Alloy only ever spends a finite budget; the models differ in what it is spent ON.
 */

open util/ordering[Tick]

/** Tick — model time: the ordinal position of an event in the history (no magnitude). */
sig Tick {}

/** Tray — a physical tray (the stacked element). */
sig Tray {}

// ══ MODEL 2 — the reified log: events are ATOMS, state is a PROJECTION ══════════════════════════════

/** StackOp — one event in the history, at its own tick. */
abstract sig StackOp { tick: one Tick }
fact OneOpPerTick { all disj a, b: StackOp | a.tick != b.tick }

/** PushOp — a tray is stacked (an event; could carry `by`, `at`, a Decision — provenance is a field). */
sig PushOp extends StackOp { tray: one Tray }

/** PopOp — the top tray is taken; `pops` names WHICH push it retires (the log is self-describing). */
sig PopOp extends StackOp { pops: one PushOp }

/** liveAmong — the pushes still on the stack after exactly the events `os`: pushed, not yet popped.
    The stack "content" is DERIVED — no structure holds it. The LIFO order is the tick order itself. */
fun liveAmong[os: set StackOp]: set PushOp {
  { q: PushOp & os | no p: PopOp & os | p.pops = q }
}

/** contentAt — the projection at a tick: fold the log prefix strictly before `t`. */
fun contentAt[t: Tick]: set PushOp { liveAmong[{ o: StackOp | lt[o.tick, t] }] }

/** topAmong — the latest live push: the maximum of the live set in tick order. */
fun topAmong[os: set StackOp]: lone PushOp {
  { q: liveAmong[os] | no r: liveAmong[os] | lt[q.tick, r.tick] }
}

// The log's LIFO discipline, stated as first-order LAW (the structural free ride `seq` gives Model 1
// must be legislated here — the price of dissolving the state structure):
fact PopDiscipline {
  all p: PopOp | {
    p.pops in liveAmong[{ o: StackOp | lt[o.tick, p.tick] }]   // only a live tray can be taken…
    p.pops = topAmong[{ o: StackOp | lt[o.tick, p.tick] }]     // …and only from the TOP (LIFO)
  }
  all q: PushOp | lone pops.q                                   // a tray placement is taken once
}

// ══ MODEL 1 — `var`/LTL: state is HELD and STEPPED; here, a REPLAY of the same log ══════════════════
// The trace consumes the log in tick order: one event per step, then stutters. Note the frame
// obligations (`done' = …`, `stack' = …`) — every step must say what changes AND what it becomes;
// the projection model above has no per-step frame at all (state is recomputed, not maintained).

one sig Replay {
  var done:  set StackOp,   // events already replayed
  var stack: seq PushOp     // the HELD state: Model 1's stack structure (top = first)
}

pred stepReplay {
  some o: StackOp - Replay.done | {
    o.tick = min[(StackOp - Replay.done).tick]        // strictly in tick order
    Replay.done' = Replay.done + o
    o in PushOp implies Replay.stack' = insert[Replay.stack, 0, o]
    o in PopOp  implies Replay.stack' = Replay.stack.rest
  }
}
pred settled {
  Replay.done = StackOp and Replay.done' = Replay.done and Replay.stack' = Replay.stack
}
fact ReplayMachine {
  no Replay.done and no Replay.stack        // starts empty
  always (stepReplay or settled)            // every step replays the next event, or stutters at the end
}

// ── it works (expect SAT) ───────────────────────────────────────────────────────────────────────────
// A history push·push·pop·push exists; the pop, by discipline, retired the SECOND push (LIFO).
run unit_ex16_history {
  some disj q1, q2, q3: PushOp, p: PopOp |
    lt[q1.tick, q2.tick] and lt[q2.tick, p.tick] and lt[p.tick, q3.tick] and p.pops = q2
} for 5 but 1..8 steps expect 1

// The replay of such a history completes, ending with two trays held.
run unit_ex16_replayCompletes {
  (some disj q1, q2: PushOp, p: PopOp | lt[q1.tick, q2.tick] and lt[q2.tick, p.tick])
  and eventually (settled and #Replay.stack = 2)
} for 5 but 1..8 steps expect 1

// ── the AGREEMENT THEOREM (check; UNSAT = holds) ────────────────────────────────────────────────────
// At every step of the trace, the HELD stack contains exactly the pushes the PROJECTION derives from
// the replayed prefix — foldl over the event list ≡ the state-monad run. The two time models agree.
assert unit_ex16_replayMatchesProjection {
  always (elems[Replay.stack] = liveAmong[Replay.done])
}
check unit_ex16_replayMatchesProjection for 5 but 1..8 steps expect 0

// And the TOPS agree: Model 1's structural top (seq head) is Model 2's derived top (max-tick live push).
assert unit_ex16_topsAgree {
  always (some Replay.stack implies Replay.stack.first = topAmong[Replay.done])
}
check unit_ex16_topsAgree for 5 but 1..8 steps expect 0

// ── the impossibility both models share (expect UNSAT) ──────────────────────────────────────────────
// Taking a tray from an empty stack is unrepresentable — in the log by PopDiscipline (no live push to
// name), and hence in the replay (rest of an empty seq never arises on a disciplined log).
run unit_ex16_popEmptyImpossible {
  some p: PopOp | no contentAt[p.tick]
} for 5 but 1..8 steps expect 0
