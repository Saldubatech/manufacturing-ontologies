module resources/tests/kanban_card

open meta/kernel
open meta/values
open reference_data/item
open resources/kanban_card

/*
 * Unit suite for the Kanban Card. Idiom: one SAT scenario proving a coherent card
 * exists, plus UNSAT scenarios proving each tight invariant forbids the bad case
 * (the §6 "constrain maximally" pattern — UNSAT = impossible).
 */

// SAT: a coherent card whose item handle resolves to an in-scope Item, with a
// last event and a consistent status.
pred unit_kanbanCard_coherent {
  some c: KanbanCard | {
    some i: Item | resolve[c.itemRef] = i
    some c.lastEvent
    some c.status
  }
}
run unit_kanbanCard_coherent for 6 but 5 Int

// UNSAT: a card whose status disagrees with the result of its last state-changing
// event (DT-001.02 (b) operational snapshot consistency).
pred unit_kanbanCard_badStatusPairing {
  some c: KanbanCard |
    some c.lastEvent and some produces[c.lastEvent.type]
      and c.status != produces[c.lastEvent.type]
}
run unit_kanbanCard_badStatusPairing for 6 but 5 Int

// UNSAT: a card whose print status disagrees with its last print event's result.
pred unit_kanbanCard_badPrintPairing {
  some c: KanbanCard |
    some c.lastPrintEvent and some printProduces[c.lastPrintEvent.type]
      and c.printStatus != printProduces[c.lastPrintEvent.type]
}
run unit_kanbanCard_badPrintPairing for 6 but 5 Int

// UNSAT: a card referencing an Item in a different tenant (kernel cross-tenant
// isolation — the item handle is in dataRefs and Item is Scoped).
pred unit_kanbanCard_crossTenantItem {
  some c: KanbanCard | let i = resolve[c.itemRef] |
    some i and i in Item and i.tenantId != c.tenantId
}
run unit_kanbanCard_crossTenantItem for 6 but 5 Int

// UNSAT: two cards sharing a serial number within one tenant.
pred unit_kanbanCard_serialClashInTenant {
  some disj a, b: KanbanCard | a.tenantId = b.tenantId and a.serialNumber = b.serialNumber
}
run unit_kanbanCard_serialClashInTenant for 6 but 5 Int
