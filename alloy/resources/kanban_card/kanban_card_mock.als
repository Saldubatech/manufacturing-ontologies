module resources/kanban_card/kanban_card_mock

/*
 * KanbanCard/CardCycle — MOCK (DT-017): what a consumer's UNIT root opens (never together with
 * the implementation — lint-guarded). Assumes the published contract; kinds, records, and reads
 * come from the types.
 */

open resources/kanban_card/kanban_card_types
open resources/kanban_card/kanban_card_contracts

fact KanbanContractAssumed { guarantees }
