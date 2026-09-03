module meta/occurrence/occurrence

/*
 * Occurrence — something that happens: an entry in the LOG, at a position in MODEL TIME (`tick`).
 *
 * MINIMAL BY DESIGN (DT-011, 2026-07-02): the core carries ONLY the causal position. The domain-time
 * stamp (`at: Instant`) is the OPT-IN subset extension `meta/occurrence/timed` — most log reasoning
 * (chaining, projections, guards) never needs wall-clock time, and carrying it by default put the
 * whole Instant family (and the two-clock bridge premise) into every log universe. Open `timed` where
 * chronological reads (period bucketing, staleness, as-of-wall-time) are actually wanted.
 */

open meta/model_time/model_time   // Tick, precedes, follows, notAfter

/** Occurrence — something that happens: a model-time (causal) position in the log, with an
    optional free-text annotation of the act itself. */
abstract sig Occurrence {
  tick: one Tick,        // model time — WHERE in the causal order
  note: lone String,     // occurrence-level annotation (MP unification ruling, 2026-08-10):
                         //   an INERT, uninterpreted payload — no law may read its content.
                         //   Built-in String: ZERO atoms in any command without string
                         //   literals, so the whole log cone carries the seat for free.
                         //   Immutable with the occurrence (acts never change after commit).
                         //   Distinct from RECORD-carried notes (shared/note's `Note` atoms
                         //   on state records — LOCF-read, freeze-governed).
  arche: one Occurrence  // ORIGIN identity (DT-029 E1; MP 2026-08-28: "use arche across the board"; TOTAL since
                         //   MP's D13 ruling A, 2026-09-03 — "first hand: my ruling is A"): the
                         //   occurrence this one originates from — the immediate CALLER's context, i.e. the
                         //   caller's own RESERVE row when this row is the leg of an intent (meta/intent_log).
                         //   SELF-INITIATED means the row cites ITSELF (`o.arche = o`, `selfInitiated`): no
                         //   caller context; the runtime's NOT-NULL `arche_id` column carries the row's own id
                         //   (MP 3.1: no branch, no null) and maps to this field by IDENTITY — `arche_id = id`
                         //   IS `o.arche = o`, no encoding between model and column (D-4 as reversed by A).
                         //   Uniqueness is per (arche, SUBJECT) and is a FACT of
                         //   meta/subject_log (`ArcheUnique`, D-3 as amended by Q8 2026-09-03); no root / audit column ever exists (MP 3.2: the call tree is walkable
                         //   through this one field).
}

/** Ticks linearize occurrences — at most one occurrence per tick — so the causal order is a strict
    total order on occurrences (not merely on the underlying ticks). */
fact OneOccurrencePerTick { all disj a, b: Occurrence | a.tick != b.tick }

/** occPrecedes — the causal (model-time) order lifted to occurrences. */
pred occPrecedes[a, b: Occurrence] { precedes[a.tick, b.tick] }

/** selfInitiated — the occurrences that cite THEMSELVES: no caller context. The self-loop is the ONE spelling
    of "self-initiated" — the field is total, like the runtime column (MP's D13 ruling A, 2026-09-03). */
fun selfInitiated: set Occurrence { { o: Occurrence | o.arche = o } }

/** A CITED origin is STRICTLY earlier than the occurrence citing it: origins never point forward; the only
    occurrence an occurrence may cite at its own tick is itself (self-initiation, exempt below). Proper cycles
    are a THEOREM of strict precedence, checked in the tests (unit_occ_archeNoProperCycle), never a fact. The
    one universal, cheap truth about origins — everything else about `arche` is adopted per log
    (meta/subject_log) or derived per pattern (meta/intent_log). */
fact ArcheOriginPrecedes { all o: Occurrence | o.arche != o implies precedes[o.arche.tick, o.tick] }
