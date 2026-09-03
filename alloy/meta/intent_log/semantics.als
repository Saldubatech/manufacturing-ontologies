module meta/intent_log/semantics

/*
 * INTENT LOG — the shared VOCABULARY of the intent-log pattern (DT-027, SAMWISE stream):
 * the CONFIRM-semantics markers an instance is parameterized with, the phases a key's
 * intent chain moves through, the peer view a re-drive reads, the re-drive verdicts, and
 * the refusal reasons. Non-parametric on purpose: every instantiation of
 * meta/intent_log/intent_log[Key, Sem] shares these atoms, so a root that opens two
 * instances (a HOLD chain and a MOVEMENT chain) speaks one vocabulary.
 *
 * ABSTRACTION (DT-013): "a module that must act on a PEER's log first reserves the key on a
 * log it owns, acts once, then confirms or releases; recovery is a function of two heads."
 */

open meta/action/outcome   // Reason
open meta/action/stateful  // Snapshot — the IntentRecord parent below

// ── the intent-record parent (DT-029 E2) ─────────────────────────────────────────────────────────
/** IntentRecord — the common parent of EVERY instance's `IntentRec` (intent_log[Key, Sem] declares
    `sig IntentRec extends IntentRecord`). What lets one instance recognize "a row of SOME intent chain" —
    a committed row whose records are IntentRecords — without naming other instances (parametric, invisible)
    and without a free marker set (a subset sig the solver could stuff peer rows into: the E2 self-check's
    ex20 counterexample, 2026-09-03). The citation-derived view counts only rows that are NOT intent rows. */
abstract sig IntentRecord extends Snapshot {}

// ── the CONFIRM semantics — the module parameter `Sem` ──────────────────────────────────────────
/** Semantics — what CONFIRM means on an intent chain (DT-027 §5, design call 1). */
abstract sig Semantics {}
/** HoldSem — CONFIRM opens a durable custody that lasts until RELEASE; TRANSFER and sub-intents
    (acts under the hold) are admitted. Chains A (cycle claim), B-cust (pool custody), C (demand claim). */
one sig HoldSem extends Semantics {}
/** MoveSem — CONFIRM completes a one-shot movement and frees the key; no TRANSFER, no sub-intents.
    Chain B-mov (pool merge / extract). */
one sig MoveSem extends Semantics {}
/** holdSemantics — the markers under which CONFIRM opens a durable custody. An instance reads its
    own `Sem` against this SET (`Sem in holdSemantics`), never against `HoldSem` itself: parameter
    substitution makes `HoldSem in HoldSem` / `MoveSem in HoldSem` literal, and the analyzer flags
    both as a redundant subset (same value / always disjoint). */
fun holdSemantics: set Semantics { HoldSem }

// ── the phase of a key on its intent chain ──────────────────────────────────────────────────────
/** Phase — where a key stands on its intent chain (the head record's `iPhase`). */
abstract sig Phase {}
one sig I_FREE,      // no live intent: never reserved, or RELEASEd (the key is available)
        I_DONE,      // MOVEMENT confirmed: the movement landed and the key is available again
        I_RESERVED,  // RESERVE committed, the peer act not yet confirmed
        I_HELD,      // HOLD confirmed: the holder owns the key until RELEASE / TRANSFER
        I_ACTING     // HELD, with ONE sub-intent (an act under the hold) pending
        extends Phase {}
/** freePhases — the phases in which a new RESERVE is admissible. */
fun freePhases: set Phase { I_FREE + I_DONE }
/** livePhases — the phases in which the key is taken by a holder. */
fun livePhases: set Phase { I_RESERVED + I_HELD + I_ACTING }
/** heldPhases — the phases in which a HOLD is in force (sub-intents ride these). */
fun heldPhases: set Phase { I_HELD + I_ACTING }

// ── the act mode of a sub-intent ────────────────────────────────────────────────────────────────
/** ActMode — whether a sub-intent's act KEEPS the hold (startProcessing on a held cycle) or
    CLOSES it in the same occurrence (shelve: the act's confirmation IS the hold's end — one
    occurrence, so no tick reads "held, peer gone back" between the act and the release;
    MINESWEEPER review of D1 v2, point 3). */
abstract sig ActMode {}
one sig AM_KEEP, AM_CLOSE extends ActMode {}

// ── the peer view — what the re-drive reads of the peer head, relative to ONE intent ────────────
/** PeerView — the peer head classified relative to an intent (DT-027 §6): the binding a CONFIRM /
    RELEASE carries ("what the owner read of the peer at this tick"); the mapping from the real
    peer head to the view is the APPLYING module's fact — exclusive arm (a transition only this
    holder could have made) or additive arm (a peer row citing this intent's rId), DT-027 §7.
    LEVEL: the view is relative to the PENDING intent — while a sub-intent is pending (I_ACTING)
    it classifies the peer against the ACT ("the act landed": e.g. the held cart is now parked),
    not against the hold; once the sub-intent settles the view is the hold's again. */
abstract sig PeerView {}
one sig PV_UNMOVED,          // no effect attributable to this intent (for a HOLD: the peer went back)
        PV_ABSENT,           // the peer entity does not exist yet (genesis legs only)
        PV_MOVED_BY_THIS,    // the act landed and is credited to this intent
        PV_MOVED_OTHERWISE   // the peer is in a state incompatible with the intent (withdrawn, closed,
                             //   deleted, taken by another owner)
        extends PeerView {}

// ── the re-drive verdicts ───────────────────────────────────────────────────────────────────────
/** RedriveAction — the one thing a (phase, peer view) pair prescribes (DT-027 §6, the table). */
abstract sig RedriveAction {}
one sig RD_SETTLED,          // nothing to do
        RD_OWNER_REDRIVE,    // the OWNER (a later version of the same owner entity) retries the act
                             //   inline or RELEASEs on the peer's typed refusal; others: RKeyTaken + alert
        RD_GENESIS,          // perform the genesis by the pre-chosen key (idempotent by construction)
        RD_CONFIRM,          // append CONFIRM citing the peer rId — no second act (the lost-ack case)
        RD_RELEASE,          // append RELEASE (the peer went elsewhere before the act)
        RD_RELEASE_DETACH,   // append RELEASE and detach on the owner side (the R7 reaction generalized)
        RD_ACT_CONFIRM,      // the pending sub-intent landed: append ACT_CONFIRM
        RD_ACT_RELEASE,      // the pending sub-intent cannot land: append ACT_RELEASE (then re-evaluate the hold)
        RD_LATE_ACT_ALERT,   // additive peers: a row cites a RELEASEd intent — alert + reversing movement
        RD_NOT_DEFINABLE     // the pair cannot arise under the pattern's rules (exclusive arm / no genesis under a hold)
        extends RedriveAction {}

// ── refusal reasons (shared by every instance; reason-precise, DT-017) ──────────────────────────
one sig RKeyTaken,          // RESERVE on a key with a live intent (the fork loser's typed outcome)
        RNotReserved,       // CONFIRM / RELEASE with no reservation or hold to confirm or release
        RWrongHolder,       // the acting holder is not the one the head names
        RNotLanded,         // CONFIRM while the peer view is not moved-by-this (nothing to cite)
        RLanded,            // RELEASE while the peer view IS moved-by-this (rule R1: release only on a typed refusal)
        RNotHoldSemantics,  // TRANSFER / sub-intent on a MOVEMENT chain
        RNotHeld,           // TRANSFER / sub-intent while the key is not HELD
        RActPending,        // a second sub-intent, or a RELEASE / TRANSFER, while one sub-intent is pending
        RNoActPending,      // ACT_CONFIRM / ACT_RELEASE with no pending sub-intent
        RDuplicateArche     // a callee row whose cited origin (`arche != self`) a committed row on the same subject already
                            //   carries — the idempotent callee's refusal (DT-029 E1; the runtime's partial unique
                            //   index per (arche_id, subject)); condition = meta/subject_log `archeDuplicate`
        extends Reason {}
