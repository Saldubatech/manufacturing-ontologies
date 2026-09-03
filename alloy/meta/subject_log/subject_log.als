module meta/subject_log/subject_log[Subject, Rec]

/*
 * WHAT THIS OFFERS A DOMAIN MODELER (DT-013): the SPINE of a subject's operation log — declare
 * your operation kinds extending `SubjectOcc`, and the module gives you the chaining law (every
 * operation reads the subject's REAL current record — refusals included) and the as-of reads
 * (`recordAt`/`startedAt`), so your module only writes what is genuinely domain: the kinds, their
 * guards and effects, and what "closed" means for your subject.
 *
 * Extracted 2026-07-03 (DT-015 Q5) from THREE hand-built instances — the InventoryItem log
 * (DT-006), the InventoryPool membership log, and the CardCycle lifecycle log — as their common,
 * SINGLE-SUBJECT core. Parameterized over `Subject` (the entity whose history this is) and `Rec`
 * (the Snapshot subtype carrying its mutable payload); each `open` gets its OWN log spine, so
 * several subject logs coexist in one model (like keyed_sum).
 *
 * WHAT STAYS DOMAIN-SIDE (deliberately — the surface would lie otherwise):
 *  - The KINDS with their typed parameter fields and `bindings`.
 *  - The reason-precise ADMISSION guards and the witnessing fact (per-kind violation sets cannot
 *    be parameterized — Alloy has no higher-order functions; copy the two-line witness idiom).
 *  - EFFECTS (per-kind record frames) and CLOSURE/liveness semantics (tombstones, rollover,
 *    never-closes — each domain's own; build them ON `lastTouch`/`recordAt`).
 *  - MULTI-SUBJECT kinds (the InventoryItem Split/Merge per-role records): this spine is
 *    single-subject; the II log keeps its bespoke `touches`/`priorOn[o, ii]` machinery — a
 *    touches-generalized spine is a NEW design topic if a second multi-subject consumer appears.
 *
 * Usage (the CardCycle shape):
 *   open meta/subject_log/subject_log[CardCycle, CycleState] as clog
 *   sig RequestOcc extends clog/SubjectOcc { ... } { bindings = subject + ... }
 *   fact MyChain { clog/chained }               // adopt the chaining law
 *   fact MyCommit { clog/commitAlwaysAccepts }  // v1 result policy, if wanted
 *   ... guards/effects; reads via clog/recordAt[s, t] ...
 */

open meta/action/stateful     // StatefulAction (pre/post: Snapshot), committed; transitively Tick, precedes/notAfter

/** SubjectOcc — an operation occurrence on one `Subject`; `pre`/`post` are its `Rec` records. */
abstract sig SubjectOcc extends StatefulAction { subject: one Subject }
fact SubjectOccRecords { all o: SubjectOcc | (o.pre + o.post) in Rec }

/** priorOn — the latest committed occurrence on the same subject strictly before `o`. */
fun priorOn[o: SubjectOcc]: lone SubjectOcc {
  { b: SubjectOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick]
      and (no c: SubjectOcc | committed[c] and c.subject = o.subject
             and precedes[b.tick, c.tick] and precedes[c.tick, o.tick]) }
}

/** chained — THE CHAINING LAW (adopt as a fact): every occurrence — refused ones included — reads
    the subject's real current record; the first reads none. Unconditional by design: a refusal
    with a free `pre` would make reason-precise witnessing gameable. */
pred chained {
  all o: SubjectOcc | let pr = priorOn[o] | (some pr => o.pre = pr.post else no o.pre)
}

/** commitAlwaysAccepts — the v1 result policy (no commit-gate refusals yet); adopt as a fact
    until a result policy exists (the deferred ABAC/commit-guard hook). */
pred commitAlwaysAccepts { all o: SubjectOcc | some o.commit implies o.commit = Accepted }

// ── origin identity (DT-029 E1): uniqueness per (arche, subject) — ADOPTED per log, never a global fact ──
/** archeDuplicate — the guard CONDITION an applier maps to its typed refusal (the runtime's partial unique
    index per (arche_id, subject) firing): an earlier committed occurrence on this subject already carries
    this occurrence's origin. Absent origins are self-minted (`archeOf[o] = o`), so uncited rows never
    collide. CONSEQUENCE: a row citing a SELF-MINTED row on the same subject collides with it (that row's origin
    IS its own identity), so a chain's follow-up rows never cite their own chain's originator via `arche`;
    citing an already-cited row is a distinct origin (immediate cause, not a root) and is legal — tests
    `archeSelfMintedSameSubjectRefused` / `archeCitedTriggerDistinct`. A pattern deriving "who cited my
    reservation" must therefore exclude its own log's rows from the citers it counts (meta/intent_log, E2).
    Idiom, in a kind's violation set: `(log/archeDuplicate[o] => RDuplicateArche else none)` (the reason atom
    is the applier's — `meta/intent_log/semantics` names it for the pattern's logs). */
pred archeDuplicate[o: SubjectOcc] {
  some b: SubjectOcc | committed[b] and b.subject = o.subject and precedes[b.tick, o.tick] and archeOf[b] = archeOf[o]
}
/** archeUniquePerSubject — no two committed occurrences on one subject share an origin: per (arche, subject)
    BY CONSTRUCTION, so one origin may span two subjects (a transfer's paired rows, SAMWISE-S1). A THEOREM of
    `archeDuplicate` sitting in every kind's guard; adopt it as a FACT instead where a log models the index
    without modelling the refusal (D-3: opt-in — roots that ignore origins pay nothing). */
pred archeUniquePerSubject {
  all disj a, b: SubjectOcc | (committed[a] and committed[b] and a.subject = b.subject) implies archeOf[a] != archeOf[b]
}

/** lastTouch — the latest committed occurrence on `s` at-or-before `t`. */
fun lastTouch[s: Subject, t: Tick]: lone SubjectOcc {
  { o: SubjectOcc | committed[o] and o.subject = s and notAfter[o.tick, t]
      and (no b: SubjectOcc | committed[b] and b.subject = s and notAfter[b.tick, t]
             and precedes[o.tick, b.tick]) }
}
/** recordAt — LOCF of records: the subject's payload as of `t` (none before any history). */
fun recordAt[s: Subject, t: Tick]: lone Rec { lastTouch[s, t].post & Rec }
/** startedAt — the subject has committed history at-or-before `t`. */
pred startedAt[s: Subject, t: Tick] { some lastTouch[s, t] }
