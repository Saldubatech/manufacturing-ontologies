module resources/kanban_card/kanban_card

open meta/profiles/baseline          // PROFILE (DT-012): structural — identity/refs/tenancy
open meta/kernel                                  // Scoped, EntityId, resolve
open shared/values                                  // Quantity (nominalQuantity)
open meta/state_machine/machine                   // print StateMachine + firedInto
open reference_data/item/item_types                     // Item (soft-ref target; TYPES only — DT-017)
open resources/processing_network/processing_network_types  // Loop (soft-ref target; TYPES only — DT-017) [KC-MH-5]
open resources/kanban_card/card_cycle             // CardCycle (the child aggregate)
open resources/kanban_card/cycle_occurrences      // the cycle LOG (DT-015): liveCycleAt, Tick

/*
 * KanbanCard — the STATIC container (KD13): identity + durable configuration + the physical/print
 * artifact, changed only by administrative edits. All dynamic state lives on its CardCycle
 * children's OCCURRENCE LOG (cycle_occurrences.als — DT-015): `currentCycleAt` and
 * `cardInCirculationAt` are log READINGS now, and the former `LiveCycleIsOpenTail` fact is a
 * verified THEOREM of the genesis guard. Parent→child aggregation modeled exactly like
 * Item→ItemSupply: `cycles` is a direct containment relation; the ownership/ordering facts live
 * HERE in the parent (≙ ItemSupplyOwnership in item.als).
 */

// ── print lifecycle (the durable artifact — KD3; lives on the card; STAYS a machine) ─────────────
/** KanbanCardPrintStatus — print/physical-artifact state (PS_-prefixed; UNKNOWN omitted). */
abstract sig KanbanCardPrintStatus extends State {}
one sig PS_NOT_PRINTED, PS_PRINTED, PS_LOST, PS_DEPRECATED, PS_RETIRED extends KanbanCardPrintStatus {}
/** KanbanCardPrintEventType — event driving the print lifecycle (PE_-prefixed). */
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
one sig KPr_destroy   extends KPrintTransition {} { on = PE_DESTROY   and no to }
one sig KPr_none      extends KPrintTransition {} { on = PE_NONE      and no to }
fact KanbanPrintMachineDef {
  KanbanPrintMachine.states      = KanbanCardPrintStatus
  KanbanPrintMachine.signals     = KanbanCardPrintEventType
  KanbanPrintMachine.start       = PS_NOT_PRINTED
  KanbanPrintMachine.transitions = KPrintTransition
  all t: KPrintTransition | t.from = KanbanCardPrintStatus and no t.guard
}
/** KanbanCardPrintEvent — embedded snapshot of the card's last print event. */
sig KanbanCardPrintEvent { type: one KanbanCardPrintEventType }

/** CardSerial — the card's natural identifier, unique within a tenant (opaque). Named distinctly
    from inventory_item's `SerialNumber` (product-instance individualizer) to avoid a cross-module
    type clash; the field stays `serialNumber`. */
sig CardSerial {}

// ── the static card ──────────────────────────────────────────────────────────────────────
/** KanbanCard — the static container + the aggregate root of its CardCycles (KD13). */
sig KanbanCard extends Scoped {
  // identity & durable configuration (administrative edits only)
  serialNumber:    one CardSerial,               // CardSerial: distinct from inventory_item's SerialNumber
  itemRef:         one EntityId,                 // → Item (immutable classifier)
  nominalQuantity: lone Quantity,                // durable target (overridable per cycle — CycleState.sQuantityOverride)
  loopRef:         lone EntityId,                // → Loop [KC-MH-5 / KD11]
  // the physical/print artifact (durable; spans cycles)
  printStatus:     lone KanbanCardPrintStatus,
  lastPrintEvent:  lone KanbanCardPrintEvent,
  // cycle aggregation (parent→child, ≙ Item.supplies)
  cycles:          set CardCycle                 // direct containment (no back-ref)
}

// Outgoing soft references (cycles is a direct relation, kept in-tenant by CardCycleOwnership).
fact KanbanCardRefs { all k: KanbanCard | k.dataRefs = k.itemRef + k.loopRef }

// A resolved item handle is an Item; a resolved loop handle is a Loop (dangling allowed — soft ref).
fact ItemRefIntegrity { all k: KanbanCard | let i = resolve[k.itemRef] | some i implies i in Item }
fact LoopRefIntegrity { all k: KanbanCard | let l = resolve[k.loopRef] | some l implies l in Loop }

// Serial numbers are unique within a tenant.
fact SerialNumberUniqueInTenant {
  all disj a, b: KanbanCard | a.tenantId = b.tenantId implies a.serialNumber != b.serialNumber
}

// Print snapshot consistency (the print lifecycle keeps the machine + snapshot form — low churn).
fact KanbanPrintConsistency {
  all k: KanbanCard | some k.lastPrintEvent implies
    firedInto[KanbanPrintMachine, k.printStatus, k.lastPrintEvent.type]
}

// ── parent→child aggregation & ordering (≙ ItemSupplyOwnership, lives in the parent) ──────
// Each cycle belongs to exactly one card; children inherit the tenant.
fact CardCycleOwnership {
  all c: CardCycle | one k: KanbanCard | c in k.cycles
  all k: KanbanCard, c: k.cycles | c.tenantId = k.tenantId
}
// [KC-MH-2] the precededBy chain stays within the card's own cycles (siblings), and each card has a
// single chain (one head) — so a card's cycles are one totally-ordered, non-overlapping series.
fact PrecededByWithinCard {
  all k: KanbanCard, c: k.cycles | some c.precededBy implies c.precededBy in k.cycles
}
fact OneChainPerCard { all k: KanbanCard | lone { c: k.cycles | no c.precededBy } }

// Tight by default: no orphan card-local value/handle atoms.
fact NoOrphanSerialNumber   { all s: CardSerial         | s in KanbanCard.serialNumber }
fact NoOrphanPrintEvent     { all e: KanbanCardPrintEvent  | e in KanbanCard.lastPrintEvent }

// ── log readings (DT-015 Phase B — the former LiveCycleIsOpenTail fact is now a THEOREM) ────────
/** currentCycleAt — the card's live (open) cycle as of `t`. `lone` by the verified
    one-live-cycle-per-card theorem (tests/cycle_occurrences.als). */
fun currentCycleAt[k: KanbanCard, t: Tick]: set CardCycle {
  { c: k.cycles | liveCycleAt[c, t] }
}
/** cardInCirculationAt — the card has a live cycle as of `t`. AVAILABLE (KC-MH-6) ⟺ NOT in
    circulation. */
pred cardInCirculationAt[k: KanbanCard, t: Tick] { some currentCycleAt[k, t] }
