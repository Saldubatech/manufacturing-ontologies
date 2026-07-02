module resources/kanban_card/tests/kanban_card

open meta/kernel
open meta/keyed_value_algebra/keyed_order   // ringAxioms/orderAxioms (no longer re-exported by the slimmed inventory_item — DT-011)
open shared/values
open meta/state_machine/machine
open reference_data/item/item
open resources/inventory_item/inventory_item   // InventoryItem (materials soft-ref target) [KC-MH-12]
open resources/processing_network/processing_network
open resources/kanban_card/card_cycle
open resources/kanban_card/kanban_card

// `materials` now resolves to InventoryItem (card_cycle opens inventory_item), so any command that
// forces an InventoryItem atom needs the keyed_order premise for its cone/derivation facts to be
// meaningful — exactly as the inventory_item test roots assume it.
fact ScalarPremises { ringAxioms and orderAxioms }

/*
 * DRAFT unit suite for the split KanbanCard + CardCycle model [KC-MH-*]. `unit_kc_*` names keep it
 * distinct from the baseline suite. SAT = a coherent structure exists; UNSAT = an invariant forbids
 * its bad case. NOTE [KC-MH-7]: this is the ATEMPORAL structural draft — it deliberately PERMITS
 * illegal operational *sequences* (those are closed by the deferred (c)/forward-skip layer, KQ-S1).
 *
 * Machine scope (DT-003): 14 State (9 op + 5 print), 20 Signal (12 + 8), 20 Transition, 2 StateMachine, 0 Guard.
 */

// ── SAT: coherent structures ──────────────────────────────────────────────────────────────
// A card in circulation: a 2-cycle precededBy chain, currentCycle = the tail, item resolves.
run unit_kc_twoCycleChainCurrent {
  some k: KanbanCard, disj c1, c2: CardCycle | {
    k.cycles = c1 + c2
    no c1.precededBy and c2.precededBy = c1            // chain head c1 → tail c2
    c1.executionStatus = COMPLETE                       // c1 closed
    c2.executionStatus = ACTIVE                         // c2 live → the derived currentCycle (the tail)
    k.currentCycle = c2
    some i: Item | resolve[k.itemRef] = i
  }
} for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 1

// A card OUT of circulation (KC-MH-6): has a cycle (history) but no currentCycle — "AVAILABLE".
run unit_kc_outOfCirculation {
  some k: KanbanCard | some k.cycles and no k.currentCycle
} for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 1

// A loaded cycle carrying materials (typed → InventoryItem, KC-MH-12), sourced by an order (untyped — KC-MH-4).
run unit_kc_loadedCycle {
  some c: CardCycle | some c.materials and some c.sourcedBy and c.status = IN_USE
} for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 1

// A card whose loop resolves to a Loop (KC-MH-5).
run unit_kc_cardOnLoop {
  some k: KanbanCard | some l: Loop | resolve[k.loopRef] = l
} for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 1

// A cycle whose `materials` soft reference resolves to an actual InventoryItem (KC-MH-12 typed seam).
run unit_kc_materialsResolveII {
  some c: CardCycle, ii: InventoryItem | resolve[c.materials] = ii
} for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 1

// A cycle carrying TWO distinct holdings at once (KC-MH-12 SET — e.g. two lots kept separate, no Merge).
run unit_kc_multiMaterials {
  some c: CardCycle | some disj a, b: InventoryItem | (a + b) in c.materialsItems
} for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 1

// ── UNSAT: structural invariants forbid the bad case ────────────────────────────────────────
// KC-MH-12: `materials` is typed — it can never resolve to a non-InventoryItem entity.
run unit_kc_materialsNonIIImpossible {
  some c: CardCycle | let m = resolve[c.materials] | some m and m not in InventoryItem
} for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// KC-MH-6: a CardCycle can never be AVAILABLE (that is card-level).
run unit_kc_cycleAvailableImpossible {
  some c: CardCycle | c.status = AVAILABLE
} for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// Ownership: every cycle belongs to exactly one card — no orphan cycle.
run unit_kc_orphanCycleImpossible {
  some c: CardCycle | no k: KanbanCard | c in k.cycles
} for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// Ownership: a cycle shared by two cards.
run unit_kc_sharedCycleImpossible {
  some disj a, b: KanbanCard | some c: CardCycle | c in a.cycles and c in b.cycles
} for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// Ordering: the precededBy chain is acyclic.
run unit_kc_precededCycleImpossible {
  some c: CardCycle | c in c.^precededBy
} for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// Ordering: linear — no two cycles share a predecessor (no fork).
run unit_kc_forkedChainImpossible {
  some disj a, b: CardCycle | some a.precededBy and a.precededBy = b.precededBy
} for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// Ordering: precededBy stays within the same card (no cross-card link).
run unit_kc_crossCardPrecededImpossible {
  some disj a, b: KanbanCard, c: a.cycles | some c.precededBy and c.precededBy in b.cycles
} for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// The LIVE (open/current) cycle must be the TAIL (KC-MH-8/11) — not one that has a successor.
run unit_kc_liveNotTailImpossible {
  some k: KanbanCard, c: k.cycles | c.executionStatus in liveCycleStatus and (some s: k.cycles | s.precededBy = c)
} for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// At most one LIVE (open) cycle per card (KC-MH-11).
run unit_kc_twoLiveCyclesImpossible {
  some k: KanbanCard | some disj a, b: k.cycles | a.executionStatus in liveCycleStatus and b.executionStatus in liveCycleStatus
} for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// SAT: a card with an ABANDONED cycle (e.g. withdrawn mid-cycle, SQ-5) — done, so not current.
run unit_kc_abandonedCycle {
  some c: CardCycle | c.executionStatus = ABANDONED
} for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 1

// Operational snapshot consistency: status must match the last event's result.
run unit_kc_badStatusPairingImpossible {
  some c: CardCycle | some c.lastEvent and not firedInto[KanbanOpMachine, c.status, c.lastEvent.type]
} for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// Print snapshot consistency on the card.
run unit_kc_badPrintPairingImpossible {
  some k: KanbanCard | some k.lastPrintEvent and not firedInto[KanbanPrintMachine, k.printStatus, k.lastPrintEvent.type]
} for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// Serial uniqueness within a tenant.
run unit_kc_serialClashImpossible {
  some disj a, b: KanbanCard | a.tenantId = b.tenantId and a.serialNumber = b.serialNumber
} for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// Cross-tenant item reference (kernel isolation).
run unit_kc_crossTenantItemImpossible {
  some k: KanbanCard | let i = resolve[k.itemRef] | some i and i in Item and i.tenantId != k.tenantId
} for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// ── machine-level checks (generic properties on the reified machines) ───────────────────────
// Mirrors the baseline suite: every modeled state reachable, every signal live. These were lost
// in the baseline → split migration; restored so the CURRENT machines are property-checked too.
check unit_kc_opReachable    { allStatesReachable[KanbanOpMachine] }
  for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0
check unit_kc_printReachable { allStatesReachable[KanbanPrintMachine] }
  for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0
check unit_kc_opLiveSignals    { liveSignals[KanbanOpMachine] }
  for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0
check unit_kc_printLiveSignals { liveSignals[KanbanPrintMachine] }
  for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0
