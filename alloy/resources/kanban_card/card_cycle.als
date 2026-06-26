module resources/kanban_card/card_cycle

open meta/kernel                  // Scoped, EntityId
open meta/values                  // Quantity, PhysicalLocator
open meta/state_machine/machine   // State, Signal, StateMachine, firedInto
open resources/inventory_item/inventory_item  // InventoryItem (materials soft-ref target) [KC-MH-12/KQ5]

/*
 * CardCycle — one circuit of a KanbanCard around its loop (KD13). The DYNAMIC per-occurrence
 * entity: operational state + trace, the carried materials, per-cycle overrides. It is the CHILD of
 * KanbanCard; the aggregation / ownership / cross-cutting ordering facts live in the PARENT module
 * (kanban_card.als), exactly like `ItemSupplyOwnership` lives in item.als — no back-reference to the
 * parent here. The operational lifecycle lives WITH the cycle (KD3); the print lifecycle lives on the
 * card.
 *
 * DRAFT model — first structural pass. Tentative hypotheses are tagged [KC-MH-n]; see the workbook
 * `notebooks/domain-ontology/resources/kanban_card/model-draft.md`. Atemporal/structural [KC-MH-7]:
 * operational coherence is the (b) snapshot rule (status == produces[lastEvent.type]); the (c)
 * forward-skip lifecycle discipline is deferred (KQ-S1) — so this draft PERMITS illegal sequences.
 */

// ── operational lifecycle (code names; lives with the cycle — KD3) ───────────────────────
/** KanbanCardStatus — operational lifecycle state. (UNKNOWN sentinel omitted.) */
abstract sig KanbanCardStatus extends State {}
one sig AVAILABLE, REQUESTING, REQUESTED, IN_PROCESS, READY,
        FULFILLING, FULFILLED, IN_USE, DEPLETED extends KanbanCardStatus {}

/** the 8 in-circulation core states — a CardCycle is always in one of these [KC-MH-6];
    AVAILABLE is a CARD-level condition (no currentCycle), not a cycle status. */
fun coreCycleStatus: set KanbanCardStatus { KanbanCardStatus - AVAILABLE }

/** KanbanCardEventType — event driving the operational lifecycle. */
abstract sig KanbanCardEventType extends Signal {}
one sig REQUEST, ACCEPT, SHELVE, START_PROCESSING, COMPLETE_PROCESSING,
        FULFILL, RECEIVE, USE, DEPLETE, WITHDRAW, NONE, FAILED_ACTION extends KanbanCardEventType {}

one sig KanbanOpMachine extends StateMachine {}
abstract sig KOpTransition extends Transition {}
one sig KOp_request  extends KOpTransition {} { on = REQUEST             and to = REQUESTING }
one sig KOp_accept   extends KOpTransition {} { on = ACCEPT              and to = REQUESTED }
one sig KOp_shelve   extends KOpTransition {} { on = SHELVE              and to = REQUESTING }
one sig KOp_start    extends KOpTransition {} { on = START_PROCESSING    and to = IN_PROCESS }
one sig KOp_complete extends KOpTransition {} { on = COMPLETE_PROCESSING and to = READY }
one sig KOp_fulfill  extends KOpTransition {} { on = FULFILL             and to = FULFILLING }
one sig KOp_receive  extends KOpTransition {} { on = RECEIVE             and to = FULFILLED }
one sig KOp_use      extends KOpTransition {} { on = USE                 and to = IN_USE }
one sig KOp_deplete  extends KOpTransition {} { on = DEPLETE             and to = DEPLETED }
one sig KOp_withdraw extends KOpTransition {} { on = WITHDRAW            and to = AVAILABLE }
one sig KOp_none     extends KOpTransition {} { on = NONE                and no to }
one sig KOp_fail     extends KOpTransition {} { on = FAILED_ACTION       and no to }
fact KanbanOpMachineDef {
  KanbanOpMachine.states      = KanbanCardStatus
  KanbanOpMachine.signals     = KanbanCardEventType
  KanbanOpMachine.start       = AVAILABLE
  KanbanOpMachine.transitions = KOpTransition
  all t: KOpTransition | t.from = KanbanCardStatus and no t.guard
}

/** KanbanCardEvent — embedded snapshot of the cycle's last operational event. */
sig KanbanCardEvent {
  type:      one KanbanCardEventType,
  fromWhere: lone PhysicalLocator,
  toWhere:   lone PhysicalLocator
}

// ── cycle EXECUTION/health axis [KC-MH-11] — resolves SQ-3/SQ-5; SPECULATIVE state set ───────
// A second, orthogonal-ish axis (distinct from the 8-state operational `status`): the health of the
// CYCLE's execution. **The membership of this set is provisional — to be reformulated** (preview:
// three KINDS — live/operating, done, indeterminate). Unlike the operational axis it has no event
// machine; its transitions are behavioral ((c) layer): ACTIVE→COMPLETE on rollover, →ABANDONED on
// withdraw, →FORCED_RESET on a forced/lenient jump (KD9), →UNTRACKED on loss of tracking.
// (UNTRACKED, not UNKNOWN: avoids the cross-module clash with item_supply's OrderMethod.UNKNOWN now
// that this tree transitively opens inventory_item → item → item_supply; also reads more precisely.)
/** CycleExecutionStatus — the cycle's execution/health state (SPECULATIVE — KC-MH-11). */
enum CycleExecutionStatus { ACTIVE, FORCED_RESET, COMPLETE, ABANDONED, UNTRACKED }

// The three KINDS (preview grouping — also speculative). "Live" cycles are the open/current ones.
/** live/operating — the cycle is open and running (the card is in circulation). */
fun liveCycleStatus:          set CycleExecutionStatus { ACTIVE + FORCED_RESET }
/** done — the cycle has finished (normally or not). */
fun doneCycleStatus:          set CycleExecutionStatus { COMPLETE + ABANDONED }
/** indeterminate — execution condition is unclear (e.g. lost track). */
fun indeterminateCycleStatus: set CycleExecutionStatus { UNTRACKED }

// ── the cycle entity ─────────────────────────────────────────────────────────────────────
/** CardCycle — one circuit of a KanbanCard (KD13). Child of KanbanCard (parent owns it). */
sig CardCycle extends Scoped {
  status:           one KanbanCardStatus,        // operational axis: in-circulation core state (pinned below)
  executionStatus:  one CycleExecutionStatus,    // [KC-MH-11] health axis (SPECULATIVE state set)
  lastEvent:        one KanbanCardEvent,     // [KC-MH-10] always present — the cycle's genesis event is REQUEST
                                             //   (REQUEST→REQUESTING births the cycle); never "no event yet". Stream → DT-001.03.
  locator:          lone PhysicalLocator,    // current location this cycle
  quantityOverride: lone Quantity,           // overrides KanbanCard.nominalQuantity [overrides]
  materials:        set EntityId,            // → InventoryItem(s) this cycle carries [KC-MH-12: SET, typed via MaterialsRefIntegrity]
                                             //   a SET (not lone) so a cycle can carry several holdings WITHOUT forcing a Merge —
                                             //   e.g. distinct lots/expirations kept separate; consolidated total via materialsItems below.
  sourcedBy:        lone EntityId,           // → Order/PO that sourced this cycle [KC-MH-4: untyped stub]
  precededBy:       lone CardCycle           // the prior cycle [KC-MH-1: DIRECT ref — flipped from soft for clean acyclicity]
}

// dataRefs = the cycle's outgoing soft references (materials + sourcedBy). The parent→child link is
// a direct relation held by KanbanCard.cycles, so it is not a dataRef here.
fact CardCycleRefs { all c: CardCycle | c.dataRefs = c.materials + c.sourcedBy }

// [KC-MH-12 / KQ5] `materials` is a TYPED soft reference SET: whatever any element resolves to is an
// InventoryItem (dangling/cross-Universe allowed — soft ref, ≙ ItemClassifierIntegrity). The cycle may
// carry SEVERAL holdings at once (relaxed from `lone`) so it need not force a Merge to co-mingle lots;
// Split/Merge remain the InventoryItem's own concern.
fact MaterialsRefIntegrity {
  all c: CardCycle | resolve[c.materials] in InventoryItem
}

/** materialsItems — the InventoryItem holdings this cycle currently carries (the resolved, in-universe
    members of `materials`). */
fun CardCycle.materialsItems: set InventoryItem { resolve[this.materials] & InventoryItem }

// consolidatedActual — the cycle's total on-hand across its holdings = the keyed Σ of
// `materialsItems.actualQuantity`. The keyed sum-over-a-set (Σ / fold of meta/algebra add) is the SAME
// capability deferred for the inventory-count metrics (workbook DT-007); until it lands, the set of
// contributing quantities is `this.materialsItems.actualQuantity` and the fold is computed downstream.
// (Multi-unit, no cross-unit conversion — a consolidated total may span units, exactly like DT-007.)

// [KC-MH-6] a CardCycle is always in one of the 8 core states (never AVAILABLE — that is card-level).
fact CycleStatusIsCore { all c: CardCycle | c.status in coreCycleStatus }

// [KC-MH-7] (b) snapshot consistency: the cycle's status is the result of its last operational event.
// Unconditional now — every cycle has a lastEvent [KC-MH-10], so no "some lastEvent implies" guard.
fact CycleOpConsistency {
  all c: CardCycle | firedInto[KanbanOpMachine, c.status, c.lastEvent.type]
}

// [KC-MH-2] ordering — the precededBy relation is acyclic and LINEAR (each cycle has at most one
// successor; the `lone` field already gives at most one predecessor). With the same-card constraint
// in the parent, a card's cycles form a single chain.
fact PrecededByAcyclic { no c: CardCycle | c in c.^precededBy }
fact PrecededByLinear  { all p: CardCycle | lone precededBy.p }   // ≤ 1 successor

// Tight by default: every event snapshot belongs to some cycle.
fact NoOrphanCardCycleEvent { all e: KanbanCardEvent | e in CardCycle.lastEvent }
