module resources/kanban_card

open meta/kernel
open meta/values            // Quantity, PhysicalLocator
open reference_data/item    // Item (soft-ref target); transitively ItemSupply for the shared-Quantity rule

/*
 * Kanban Card — the demand signal at the heart of replenishment. Tenant-scoped
 * aggregate root. Code-faithful to the operations backend
 * (cards/arda/operations/resources/kanban, KanbanCard.kt); see the published docs:
 * https://arda-cards.github.io  →  Current System / Functional / Resources / Kanban Cards.
 *
 * Two orthogonal state machines (operational + print), each modeled per DT-001.02
 * decision (b): a constant transition table (`produces` / `printProduces`) plus a
 * snapshot-consistency invariant tying the card's current status to its last event.
 * No temporal trace and no event history — the event timestamp/author and the
 * `kanban_card_event` stream belong to the deferred bitemporal layer (DT-001.03).
 * Loop is documented but unimplemented in code, so it is not modeled here.
 */

// ---------------------------------------------------------------------------
// Operational state machine (KanbanCardStatus / KanbanCardEventType — code names)
// ---------------------------------------------------------------------------
enum KanbanCardStatus {
  AVAILABLE, REQUESTING, REQUESTED, IN_PROCESS, READY,
  FULFILLING, FULFILLED, IN_USE, DEPLETED, UNKNOWN
}
enum KanbanCardEventType {
  REQUEST, ACCEPT, SHELVE, START_PROCESSING, COMPLETE_PROCESSING,
  FULFILL, RECEIVE, USE, DEPLETE, WITHDRAW, NONE, FAILED_ACTION
}

// The status an event yields (LifecycleImpl). NONE / FAILED_ACTION are absent →
// "no change" (they leave the prior status in place).
fun produces: KanbanCardEventType -> lone KanbanCardStatus {
    REQUEST             -> REQUESTING
  + ACCEPT              -> REQUESTED
  + SHELVE              -> REQUESTING
  + START_PROCESSING    -> IN_PROCESS
  + COMPLETE_PROCESSING -> READY
  + FULFILL             -> FULFILLING
  + RECEIVE             -> FULFILLED
  + USE                 -> IN_USE
  + DEPLETE             -> DEPLETED
  + WITHDRAW            -> AVAILABLE
}

// ---------------------------------------------------------------------------
// Print state machine (KanbanCardPrintStatus / KanbanCardPrintEventType).
// Alloy enum members are GLOBAL singletons, so the print enums are prefixed
// (PS_/PE_) to avoid clashing with the operational enums (UNKNOWN, LOST, NONE).
// PS_* ↔ NOT_PRINTED/PRINTED/LOST/DEPRECATED/RETIRED/UNKNOWN;
// PE_* ↔ PRINT/REPRINT/LOST/DEPRECATE/RETIRE/DESTROY/UNMARK/NONE.
// ---------------------------------------------------------------------------
enum KanbanCardPrintStatus {
  PS_NOT_PRINTED, PS_PRINTED, PS_LOST, PS_DEPRECATED, PS_RETIRED, PS_UNKNOWN
}
enum KanbanCardPrintEventType {
  PE_PRINT, PE_REPRINT, PE_LOST, PE_DEPRECATE, PE_RETIRE, PE_DESTROY, PE_UNMARK, PE_NONE
}

// The print status an event yields (PrintLifecycleImpl). PE_DESTROY clears the status
// (→ none) and PE_NONE is "no change" — both absent here.
fun printProduces: KanbanCardPrintEventType -> lone KanbanCardPrintStatus {
    PE_PRINT     -> PS_PRINTED
  + PE_REPRINT   -> PS_PRINTED
  + PE_LOST      -> PS_LOST
  + PE_DEPRECATE -> PS_DEPRECATED
  + PE_RETIRE    -> PS_RETIRED
  + PE_UNMARK    -> PS_NOT_PRINTED
}

// ---------------------------------------------------------------------------
// Event value objects (embedded snapshots of the last lifecycle/print event).
// No identity. Code also carries atTime (TimeCoordinates) + author — deferred to
// the bitemporal layer, so not modeled here.
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

// DT-001.02 (b): operational snapshot consistency. If the last event is a
// state-changing one, the current status equals what it produces (and is present).
fact StatusMatchesLastEvent {
  all c: KanbanCard |
    (some c.lastEvent and some produces[c.lastEvent.type])
      implies c.status = produces[c.lastEvent.type]
}

// DT-001.02 (b): print snapshot consistency (PE_DESTROY/PE_NONE leave it free).
fact PrintStatusMatchesLastEvent {
  all c: KanbanCard |
    (some c.lastPrintEvent and some printProduces[c.lastPrintEvent.type])
      implies c.printStatus = printProduces[c.lastPrintEvent.type]
}

// Tight by default: no orphan value atoms owned by the card.
fact NoOrphanCardValues {
  all e: KanbanCardEvent      | e in KanbanCard.lastEvent
  all e: KanbanCardPrintEvent | e in KanbanCard.lastPrintEvent
  all s: SerialNumber         | s in KanbanCard.serialNumber
  all p: PhysicalLocator      | p in KanbanCard.locator
                                   + KanbanCardEvent.fromWhere + KanbanCardEvent.toWhere
}

// Tight by default: Quantity is now SHARED across domains (ItemSupply.orderQuantity +
// KanbanCard.cardQuantity). This module is the lowest in the open-DAG that sees both
// users, so the no-orphan-Quantity rule lives here (relocated from item_supply, §6).
fact NoOrphanQuantity {
  all q: Quantity | q in ItemSupply.orderQuantity + KanbanCard.cardQuantity
}
