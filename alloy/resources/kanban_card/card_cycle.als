module resources/kanban_card/card_cycle

open meta/profiles/baseline       // PROFILE (DT-012): structural — identity/refs/tenancy
open meta/kernel                  // Scoped, EntityId

/*
 * CardCycle — one circuit of a KanbanCard around its loop (KD13). SLIMMED to IDENTITY ONLY
 * (DT-015 Phase B, 2026-07-02): the mutable payload (status, locator, materials, quantity
 * override) lives on `CycleState` records carried by the cycle's operation occurrences
 * (cycle_occurrences.als); the operational lifecycle IS the log — `lastEvent`, the stored
 * `executionStatus` health axis (SQ-8: dissolved into the log readings live/completed/abandoned),
 * and the `KanbanOpMachine` transition table (subsumed by the forward-skip admission guards,
 * incl. the former `withdraw → AVAILABLE` arm — withdrawal is the closing tombstone occurrence)
 * are all RETIRED. The print lifecycle stays on the card (kanban_card.als).
 *
 * The aggregation / ownership / cross-cutting ordering facts live in the PARENT module
 * (kanban_card.als), exactly like `ItemSupplyOwnership` lives in item.als.
 */

// ── the operational status vocabulary (a plain enum now — the machine retired with Phase B) ─────
/** KanbanCardStatus — the operational lifecycle states. The 8 CORE states are cycle states;
    AVAILABLE is the CARD-level "no live cycle" condition (KC-MH-6) — kept in the vocabulary for
    card-level prose/readings, unrepresentable on cycle records (a CycleState fact). */
abstract sig KanbanCardStatus {}
one sig AVAILABLE, REQUESTING, REQUESTED, IN_PROCESS, READY,
        FULFILLING, FULFILLED, IN_USE, DEPLETED extends KanbanCardStatus {}

// ── the cycle entity: IDENTITY ONLY (immutable for the cycle's whole existence) ─────────────────
/** CardCycle — the identity of one circuit of a KanbanCard; child of KanbanCard (the parent owns
    it); its mutable payload lives on CycleState records in the occurrence log. */
sig CardCycle extends Scoped {
  sourcedBy:  lone EntityId,     // → Order/PO that sourced this cycle [KC-MH-4: untyped stub; DT-014 rung 3 types it]
  precededBy: lone CardCycle     // the prior cycle [KC-MH-1: DIRECT ref — flipped from soft for clean acyclicity]
}

// dataRefs = the cycle's outgoing soft references. Materials are RECORD-carried (CycleState.sMaterials)
// — not entity dataRefs; their tenancy integrity is a log-side fact (cycle_occurrences.als).
fact CardCycleRefs { all c: CardCycle | c.dataRefs = c.sourcedBy }

// [KC-MH-2] ordering — acyclic and LINEAR (each cycle ≤1 successor; the `lone` field gives ≤1
// predecessor). With the same-card constraint in the parent, a card's cycles form a single chain.
fact PrecededByAcyclic { no c: CardCycle | c in c.^precededBy }
fact PrecededByLinear  { all p: CardCycle | lone precededBy.p }   // ≤ 1 successor
