module meta/subject_log/tests/subject_log

open meta/action/stateful
open meta/subject_log/subject_log[Widget, WidgetState] as wl

/*
 * Suite for the subject-log SPINE (DT-015 Q5 extraction), exercised on a minimal local
 * instantiation: a Widget whose record carries one Int level, with a single SetLevel operation
 * (guard: non-negative). Verifies exactly what the spine OWNS — the chaining law, LOCF reads,
 * and the refusals-read-but-don't-write discipline; kinds/guards/effects are the consumer's
 * (three real ones: the InventoryItem, InventoryPool, and CardCycle logs).
 */

sig Widget {}
sig WidgetState extends Snapshot { level: one Int }
fact WidgetStateExtensional { all disj a, b: WidgetState | a.level != b.level }

one sig RNegative extends Reason {}
one sig RDuplicateArche extends Reason {}   // this root's own typed refusal for a re-sent origin (the pattern's atom lives in meta/intent_log/semantics)

sig SetLevelOcc extends wl/SubjectOcc { to: one Int } { bindings = subject + to }

fact SpineAdopted { wl/chained and wl/commitAlwaysAccepts }
fun setViol[o: SetLevelOcc]: set Reason {
  ((o.to < 0) => RNegative else none)
  + (wl/archeDuplicate[o] => RDuplicateArche else none)   // DT-029 E1: the idempotent callee's refusal
}
fact SetLevelWitness {
  all o: SetLevelOcc | (o.admission = Accepted iff no setViol[o])
    and (o.admission in Rejected implies o.admission.because = setViol[o])
}
fact SetLevelEffect { all o: SetLevelOcc | committed[o] implies o.post.level = o.to }

// ── witnesses ───────────────────────────────────────────────────────────────────────────────────
// Two committed operations chain: the second reads the first's record; LOCF reads the second.
run unit_slog_chainLoads {
  some s: Widget, disj a, b: SetLevelOcc | {
    a.subject = s and b.subject = s and precedes[a.tick, b.tick]
    committed[a] and committed[b]
    b.pre = a.post
    wl/recordAt[s, b.tick] = b.post
  }
} for 5 but 4 Int expect 1

// A refusal READS the real record (unconditional chaining) yet has no post.
run unit_slog_refusalReadsReal {
  some s: Widget, a, r: SetLevelOcc | {
    a.subject = s and r.subject = s and precedes[a.tick, r.tick]
    committed[a] and refusedAtAdmission[r] and r.admission.because = RNegative
    r.pre = a.post and no r.post
  }
} for 5 but 4 Int expect 1

// ── theorems (check; UNSAT = holds) ─────────────────────────────────────────────────────────────
// The first occurrence on a subject reads nothing.
assert unit_slog_firstReadsNothing {
  all o: wl/SubjectOcc | no wl/priorOn[o] implies no o.pre
}
check unit_slog_firstReadsNothing for 5 but 4 Int expect 0

// LOCF: the as-of read at any occurrence's tick is the latest committed post at-or-before it.
assert unit_slog_locf {
  all o: wl/SubjectOcc | committed[o] implies wl/recordAt[o.subject, o.tick] = o.post
}
check unit_slog_locf for 5 but 4 Int expect 0

// Refusals contribute nothing: the read just after a refusal equals the read just before it.
assert unit_slog_refusalContributesNothing {
  all o: wl/SubjectOcc | refusedAtAdmission[o] implies
    wl/recordAt[o.subject, o.tick] = wl/lastTouch[o.subject, o.tick].post
    and (no wl/lastTouch[o.subject, o.tick] or committed[wl/lastTouch[o.subject, o.tick]])
}
check unit_slog_refusalContributesNothing for 5 but 4 Int expect 0

// THE STATE FUNCTION (1:1 in the subject→record direction): once a subject has committed
// history, it has EXACTLY ONE current record at every instant — recordAt is a total function of
// (started subject, tick). Derived, not assumed: lastTouch is unique (one occurrence per tick,
// ticks totally ordered) and a committed occurrence always has a post (PostOnlyIfCommitted).
// NB the converse direction is deliberately NOT 1:1 — records are extensional VALUES, shared
// across subjects and times (two subjects in identical conditions share one record atom).
assert unit_slog_recordIsFunctionOnceStarted {
  all s: Widget, t: Tick |
    (wl/startedAt[s, t] implies one wl/recordAt[s, t])
    and (not wl/startedAt[s, t] implies no wl/recordAt[s, t])
}
check unit_slog_recordIsFunctionOnceStarted for 5 but 4 Int expect 0

// The chaining thread is committed-only: an occurrence's pre is always a COMMITTED predecessor's post.
assert unit_slog_threadIsCommitted {
  all o: wl/SubjectOcc | some o.pre implies committed[wl/priorOn[o]]
}
check unit_slog_threadIsCommitted for 5 but 4 Int expect 0

// ── origin identity (DT-029 E1): per (arche, subject), adopted by this log through its guard ───────
// A second operation re-sending an origin already committed on the widget is refused RDuplicateArche;
// the first stands (the lost-reply retry lands exactly once).
run unit_slog_archeDuplicateRefused {
  some w: Widget, o: SetLevelOcc, disj a, b: SetLevelOcc |
    committed[o] and o.subject != w and committed[a] and refusedAtAdmission[b] and b.admission.because = RDuplicateArche
    and a.subject = w and b.subject = w and a.arche = o and b.arche = o
    and precedes[o.tick, a.tick] and precedes[a.tick, b.tick]
} for 5 but 4 Int expect 1

// One origin may span TWO subjects (a transfer's paired rows, SAMWISE-S1): uniqueness is per (arche, subject).
run unit_slog_archeTwoSubjectsOneArche {
  some o: SetLevelOcc, disj a, b: SetLevelOcc |
    committed[o] and committed[a] and committed[b] and a.subject != b.subject
    and a.arche = o and b.arche = o and o.subject != a.subject and o.subject != b.subject
} for 5 but 4 Int expect 1

// A same-subject reaction may cite a SELF-MINTED row (E1 as amended on MINESWEEPER's review, 2026-09-03): the
// row's own identity never occupies a uniqueness slot — the law is over CITATIONS, one-for-one with the
// runtime's partial index. (The first E1 cut forbade this; the negative witness it carried was retired.)
run unit_slog_archeSelfMintedReactionAllowed {
  some w: Widget, o, a: SetLevelOcc | committed[o] and o.arche = o and committed[a] and o.subject = w and a.subject = w and a.arche = o
} for 5 but 4 Int expect 1

// But citing an already-CITED row on the same subject is a DISTINCT origin (immediate cause, not a root — MP 3.2),
// so it is legal: the first run of this pair was written as "never along a chain" and the solver refuted it
// (2026-09-03) with exactly this instance. Recorded as a witness so the semantics stay visible.
run unit_slog_archeCitedTriggerDistinct {
  some w: Widget, x, o, a: SetLevelOcc | committed[x] and committed[o] and committed[a]
    and o.subject = w and a.subject = w and o.arche = x and a.arche = o
} for 5 but 4 Int expect 1

// The uniqueness predicate is a THEOREM of the refusal sitting in the guard (D-3: adopt it as a fact only where
// a log models the index without modelling the refusal).
assert unit_slog_archeUniqueTheorem { wl/archeUniquePerSubject }
check unit_slog_archeUniqueTheorem for 5 but 4 Int expect 0
