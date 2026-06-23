module resources/kanban_card

open meta/kernel
open meta/values                 // Quantity, PhysicalLocator
open meta/state_machine/machine  // State, Signal, StateMachine, firedInto, …
open reference_data/item         // Item (soft-ref target); transitively ItemSupply for the shared-Quantity rule

/*
 * Kanban Card — the demand signal at the heart of replenishment. Tenant-scoped
 * aggregate root. Code-faithful to the operations backend
 * (cards/arda/operations/resources/kanban, KanbanCard.kt); see the published docs:
 * https://arda-cards.github.io  →  Current System / Functional / Resources / Kanban Cards.
 *
 * Two orthogonal state machines (operational + print). Each is a REIFIED
 * StateMachine (meta/state_machine, DT-003), so the generic well-formedness,
 * determinism, reachability and live-signal properties apply uniformly; the
 * snapshot-consistency rule (DT-001.02 (b)) is the generic `firedInto`. No temporal
 * trace / event history — event timestamp/author and the kanban_card_event stream
 * belong to the deferred bitemporal layer (DT-001.03). Loop is documented but
 * unimplemented in code, so it is not modeled here.
 */

// ---------------------------------------------------------------------------
// Operational state machine (KanbanCardStatus / KanbanCardEventType — code names).
// Enums are the long form (abstract sig + one sigs) so they extend State/Signal.
// ---------------------------------------------------------------------------
// (Code's KanbanCardStatus.UNKNOWN is a null/unknown sentinel — an implementation
// artifact, not a lifecycle state — so it is omitted from the model.)
abstract sig KanbanCardStatus extends State {}
one sig AVAILABLE, REQUESTING, REQUESTED, IN_PROCESS, READY,
        FULFILLING, FULFILLED, IN_USE, DEPLETED extends KanbanCardStatus {}

abstract sig KanbanCardEventType extends Signal {}
one sig REQUEST, ACCEPT, SHELVE, START_PROCESSING, COMPLETE_PROCESSING,
        FULFILL, RECEIVE, USE, DEPLETE, WITHDRAW, NONE, FAILED_ACTION extends KanbanCardEventType {}

one sig KanbanOpMachine extends StateMachine {}
abstract sig KOpTransition extends Transition {}
// Code's LifecycleImpl maps event → state regardless of current state, so every
// transition's `from` is ANY (all states; pinned in the machine fact below).
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
one sig KOp_none     extends KOpTransition {} { on = NONE                and no to }   // "no change"
one sig KOp_fail     extends KOpTransition {} { on = FAILED_ACTION       and no to }   // "no change"
fact KanbanOpMachineDef {
  KanbanOpMachine.states      = KanbanCardStatus
  KanbanOpMachine.signals     = KanbanCardEventType
  KanbanOpMachine.start       = AVAILABLE
  KanbanOpMachine.transitions = KOpTransition
  all t: KOpTransition | t.from = KanbanCardStatus and no t.guard   // ANY source, no guards
}

// ---------------------------------------------------------------------------
// Print state machine. Alloy enum members are GLOBAL singletons, so print states/
// signals are PS_/PE_-prefixed to avoid clashing with the operational ones
// (LOST, NONE). PS_* ↔ NOT_PRINTED/PRINTED/LOST/DEPRECATED/RETIRED;
// PE_* ↔ PRINT/REPRINT/LOST/DEPRECATE/RETIRE/DESTROY/UNMARK/NONE.
// (Code's KanbanCardPrintStatus.UNKNOWN is a null sentinel — omitted, as above.)
// ---------------------------------------------------------------------------
abstract sig KanbanCardPrintStatus extends State {}
one sig PS_NOT_PRINTED, PS_PRINTED, PS_LOST, PS_DEPRECATED, PS_RETIRED
        extends KanbanCardPrintStatus {}

abstract sig KanbanCardPrintEventType extends Signal {}
one sig PE_PRINT, PE_REPRINT, PE_LOST, PE_DEPRECATE, PE_RETIRE, PE_DESTROY, PE_UNMARK, PE_NONE
        extends KanbanCardPrintEventType {}

one sig KanbanPrintMachine extends StateMachine {}
abstract sig KPrintTransition extends Transition {}
one sig KPr_print     extends KPrintTransition {} { on = PE_PRINT     and to = PS_PRINTED }
one sig KPr_reprint   extends KPrintTransition {} { on = PE_REPRINT   and to = PS_PRINTED }
one sig KPr_lost      extends KPrintTransition {} { on = PE_LOST      and to = PS_LOST }
one sig KPr_deprecate extends KPrintTransition {} { on = PE_DEPRECATE and to = PS_DEPRECATED }
one sig KPr_retire    extends KPrintTransition {} { on = PE_RETIRE    and to = PS_RETIRED }
one sig KPr_unmark    extends KPrintTransition {} { on = PE_UNMARK    and to = PS_NOT_PRINTED }
one sig KPr_destroy   extends KPrintTransition {} { on = PE_DESTROY   and no to }   // clears status → modeled "no change"
one sig KPr_none      extends KPrintTransition {} { on = PE_NONE      and no to }   // "no change"
fact KanbanPrintMachineDef {
  KanbanPrintMachine.states      = KanbanCardPrintStatus
  KanbanPrintMachine.signals     = KanbanCardPrintEventType
  KanbanPrintMachine.start       = PS_NOT_PRINTED
  KanbanPrintMachine.transitions = KPrintTransition
  all t: KPrintTransition | t.from = KanbanCardPrintStatus and no t.guard
}

// ---------------------------------------------------------------------------
// Event value objects (embedded snapshots of the last lifecycle/print event).
// No identity. Code also carries atTime (TimeCoordinates) + author — deferred to
// the bitemporal layer, so not modeled here. `type` is the driving Signal.
// ---------------------------------------------------------------------------
sig KanbanCardEvent {
  type:      one KanbanCardEventType,
  fromWhere: lone PhysicalLocator,
  toWhere:   lone PhysicalLocator
}
sig KanbanCardPrintEvent {
  type: one KanbanCardPrintEventType
}

// Serial number — the card's natural identifier (unique within tenant). Opaque
// handle (code: String); identity for the model is still the kernel eId.
sig SerialNumber {}

// ---------------------------------------------------------------------------
// The aggregate root.
// ---------------------------------------------------------------------------
sig KanbanCard extends Scoped {
  serialNumber:   one SerialNumber,
  itemRef:        one EntityId,            // soft ref → Item (code: ItemReference handle)
  cardQuantity:   lone Quantity,
  locator:        lone PhysicalLocator,
  status:         lone KanbanCardStatus,
  printStatus:    lone KanbanCardPrintStatus,
  lastEvent:      lone KanbanCardEvent,
  lastPrintEvent: lone KanbanCardPrintEvent
}

// Outgoing soft references: just the item handle. (tenantId is added by the kernel's
// derived `refs`, so cross-tenant isolation already covers the item link.)
fact KanbanCardRefs { all c: KanbanCard | c.dataRefs = c.itemRef }

// Tight by default: a resolved item handle must actually be an Item. (Dangling /
// cross-Universe refs are still allowed — the soft-reference case.)
fact ItemRefIntegrity {
  all c: KanbanCard | let i = resolve[c.itemRef] | some i implies i in Item
}

// Business rule: serial numbers are unique within a tenant (code: KanbanCardService).
fact SerialNumberUniqueInTenant {
  all disj a, b: KanbanCard | a.tenantId = b.tenantId implies a.serialNumber != b.serialNumber
}

// DT-001.02 (b), reified: a card's status is consistent with the result of its last
// operational event (and is forced present when that event is state-changing).
fact KanbanOpConsistency {
  all c: KanbanCard | some c.lastEvent implies
    firedInto[KanbanOpMachine, c.status, c.lastEvent.type]
}
fact KanbanPrintConsistency {
  all c: KanbanCard | some c.lastPrintEvent implies
    firedInto[KanbanPrintMachine, c.printStatus, c.lastPrintEvent.type]
}

// Tight by default: no orphan value atoms owned by the card. Quantity and
// PhysicalLocator are SHARED value objects (used across modules) and are therefore
// orphan-EXEMPT (DT-004 Q8) — only the card-local handles are constrained here.
fact NoOrphanCardValues {
  all e: KanbanCardEvent      | e in KanbanCard.lastEvent
  all e: KanbanCardPrintEvent | e in KanbanCard.lastPrintEvent
  all s: SerialNumber         | s in KanbanCard.serialNumber
}
