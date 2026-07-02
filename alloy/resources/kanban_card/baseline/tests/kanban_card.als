module resources/kanban_card/baseline/tests/kanban_card

open meta/kernel
open shared/values
open meta/state_machine/machine
open reference_data/item/item
open resources/kanban_card/baseline/kanban_card

/*
 * Unit suite for the Kanban Card. Idiom: SAT scenarios prove coherent cards/machines
 * exist; UNSAT scenarios prove each tight invariant forbids its bad case (§6).
 *
 * Scope note (DT-003): the reified one-sig families are exact — 14 State (9 op + 5
 * print), 20 Signal (12 + 8), 20 Transition, 2 StateMachine, 0 Guard — so the
 * commands pin those and leave the variable entity sigs at 6.
 */

// SAT: a coherent card whose item handle resolves to an in-scope Item, with a last
// event and a consistent status.
pred unit_kanbanCard_coherent {
  some c: KanbanCard | {
    some i: Item | resolve[c.itemRef] = i
    some c.lastEvent
    some c.status
  }
}
run unit_kanbanCard_coherent
  for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int expect 1

// UNSAT: a card whose status is not a valid result of its last operational event.
pred unit_kanbanCard_badStatusPairing {
  some c: KanbanCard | some c.lastEvent and not firedInto[KanbanOpMachine, c.status, c.lastEvent.type]
}
run unit_kanbanCard_badStatusPairing
  for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int expect 0

// UNSAT: a card whose print status is not a valid result of its last print event.
pred unit_kanbanCard_badPrintPairing {
  some c: KanbanCard | some c.lastPrintEvent and not firedInto[KanbanPrintMachine, c.printStatus, c.lastPrintEvent.type]
}
run unit_kanbanCard_badPrintPairing
  for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int expect 0

// UNSAT: a card referencing an Item in a different tenant (kernel cross-tenant isolation).
pred unit_kanbanCard_crossTenantItem {
  some c: KanbanCard | let i = resolve[c.itemRef] |
    some i and i in Item and i.tenantId != c.tenantId
}
run unit_kanbanCard_crossTenantItem
  for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int expect 0

// UNSAT: two cards sharing a serial number within one tenant.
pred unit_kanbanCard_serialClashInTenant {
  some disj a, b: KanbanCard | a.tenantId = b.tenantId and a.serialNumber = b.serialNumber
}
run unit_kanbanCard_serialClashInTenant
  for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard, 5 Int expect 0

// --- machine-level checks (generic properties on the reified machines) -------
// Every modeled lifecycle state is reachable from the start, and every signal is
// live. (The code's UNKNOWN/PS_UNKNOWN sentinels are not modeled, so there is no
// unreachable carve-out.)
check unit_kanbanOp_reachable    { allStatesReachable[KanbanOpMachine] }
  for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard expect 0
check unit_kanbanPrint_reachable { allStatesReachable[KanbanPrintMachine] }
  for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard expect 0
check unit_kanbanOp_liveSignals    { liveSignals[KanbanOpMachine] }
  for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard expect 0
check unit_kanbanPrint_liveSignals { liveSignals[KanbanPrintMachine] }
  for 6 but 14 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard expect 0
