module resources/kanban_card/tests/kanban_card

open meta/kernel
open shared/values
open meta/state_machine/machine
open reference_data/item/item
open resources/inventory_item/inventory_item   // InventoryItem (materials soft-ref target) [KC-MH-12]
open resources/processing_network/processing_network
open resources/kanban_card/card_cycle
open resources/kanban_card/cycle_occurrences
open resources/kanban_card/kanban_card

/*
 * Structural suite for the split KanbanCard + CardCycle model — SLIMMED with DT-015 Phase B: the
 * operational lifecycle moved to the occurrence log (tests/cycle_occurrences.als carries the
 * behavioral claims: guards, closure, one-live-per-card); this root keeps the STRUCTURAL laws
 * (identity, ownership, ordering, refs, the print machine) plus the log-composed card readings.
 * Premises are FACTS via the P1 profile in the cone (the à la carte ScalarPremises fact retired).
 * Machine pins: 5 State / 8 Signal / 8 Transition / 1 StateMachine (print only — the op machine
 * retired). 5 Int: the region ranks reach 8.
 */

// ── SAT: coherent structures ──────────────────────────────────────────────────────────────
// A card in circulation: a 2-cycle chain, c1 closed by ROLLOVER, currentCycleAt = the tail (log).
run unit_kc_twoCycleChainCurrent {
  some k: KanbanCard, disj c1, c2: CardCycle, r2: RequestOcc | {
    k.cycles = c1 + c2
    no c1.precededBy and c2.precededBy = c1
    r2.cycle = c2 and committed[r2]
    currentCycleAt[k, r2.tick] = c2
    some i: Item | resolve[k.itemRef] = i
  }
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 1

// A card OUT of circulation (KC-MH-6): it has cycle history but no live cycle — "AVAILABLE".
run unit_kc_outOfCirculation {
  some k: KanbanCard, t: Tick | some k.cycles and not cardInCirculationAt[k, t]
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 1

// A loaded cycle: IN_USE carrying materials (record-carried since Phase B), sourced by an order.
run unit_kc_loadedCycle {
  some c: CardCycle, t: Tick | {
    statusAt[c, t] = IN_USE
    some stateOfCycleAt[c, t].sMaterials
    some c.sourcedBy
  }
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar, 2 InventoryItem expect 1

// A card whose loop resolves to a Loop (KC-MH-5).
run unit_kc_cardOnLoop {
  some k: KanbanCard | some l: Loop | resolve[k.loopRef] = l
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 1

// A received material resolves to an actual InventoryItem (KC-MH-12 typed seam, via the record).
run unit_kc_materialsResolveII {
  some o: ReceiveOcc, ii: InventoryItem | committed[o] and resolve[o.materials] = ii
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar, 2 InventoryItem expect 1

// A cycle carrying TWO distinct holdings at once (KC-MH-12 SET — e.g. two lots, no Merge forced).
run unit_kc_multiMaterials {
  some c: CardCycle, t: Tick | some disj a, b: InventoryItem |
    (a + b) in resolve[stateOfCycleAt[c, t].sMaterials]
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar, 2 InventoryItem expect 1

// ── UNSAT: structural invariants forbid the bad case ────────────────────────────────────────
// KC-MH-12: received materials are typed — they can never resolve to a non-InventoryItem entity.
run unit_kc_materialsNonIIImpossible {
  some o: ReceiveOcc | let m = resolve[o.materials] | some m and m not in InventoryItem
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// KC-MH-6: a cycle STATE can never be AVAILABLE (that is card-level; a CycleState record fact).
run unit_kc_cycleAvailableImpossible {
  some s: CycleState | s.sStatus = AVAILABLE
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// Ownership: every cycle belongs to exactly one card — no orphan cycle.
run unit_kc_orphanCycleImpossible {
  some c: CardCycle | no k: KanbanCard | c in k.cycles
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// Ownership: a cycle shared by two cards.
run unit_kc_sharedCycleImpossible {
  some disj a, b: KanbanCard | some c: CardCycle | c in a.cycles and c in b.cycles
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// Ordering: the precededBy chain is acyclic.
run unit_kc_precededCycleImpossible {
  some c: CardCycle | c in c.^precededBy
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// Ordering: linear — no two cycles share a predecessor (no fork).
run unit_kc_forkedChainImpossible {
  some disj a, b: CardCycle | some a.precededBy and a.precededBy = b.precededBy
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// Ordering: precededBy stays within the same card (no cross-card link).
run unit_kc_crossCardPrecededImpossible {
  some disj a, b: KanbanCard, c: a.cycles | some c.precededBy and c.precededBy in b.cycles
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// (The live-cycle laws — one live per card, live = open tail — are THEOREMS of the log now:
// see tests/cycle_occurrences.als `unit_cyc_oneLiveCyclePerCard` and the closure suite.)

// Print snapshot consistency on the card (the print lifecycle keeps the machine form).
run unit_kc_badPrintPairingImpossible {
  some k: KanbanCard | some k.lastPrintEvent and not firedInto[KanbanPrintMachine, k.printStatus, k.lastPrintEvent.type]
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// Serial uniqueness within a tenant.
run unit_kc_serialClashImpossible {
  some disj a, b: KanbanCard | a.tenantId = b.tenantId and a.serialNumber = b.serialNumber
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// Cross-tenant item reference (kernel isolation).
run unit_kc_crossTenantItemImpossible {
  some k: KanbanCard | let i = resolve[k.itemRef] | some i and i in Item and i.tenantId != k.tenantId
} for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0

// ── machine-level checks (the PRINT machine — the op machine retired with DT-015 Phase B) ────
check unit_kc_printReachable { allStatesReachable[KanbanPrintMachine] }
  for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0
check unit_kc_printLiveSignals { liveSignals[KanbanPrintMachine] }
  for 6 but 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard, 5 Int, 3 Scalar expect 0
