module soak/sliced/receiving_soak

/*
 * SOAK tier (DT-022 TQ-5): the receiving freeze + lattice laws at GENEROUS scopes — see
 * kanban_soak.als for the tier's rationale. `make soak` only; never on the push path.
 */

open receiving/receiver/receiver_implementation
open receiving/receiver/receiver_contracts
open operations/demand/demand_mock
open procurement/order/order_mock
open reference_data/item/item_mock
open reference_data/business_affiliate/business_affiliate_mock
open resources/processing_network/processing_network_mock
open resources/kanban_card/kanban_card_mock
open resources/inventory_item/inventory_item_mock
open reference_data/staff/staff_mock

// RETIRED (MP signoff 2026-08-28, DT-024 E7 ladder window 2): `soak_rcv_capturedFactsFrozen`
// — LC-RCV-03 is PROVEN INDUCTIVE as a per-occurrence rung
// (receiver_captured_facts_inductive.als: slice-faithful + base + step + law, state-local;
// both scope gates green 2026-08-27; vacuity guards SAT 2026-08-28), superseding the trace
// search at these scopes. This root now carries no commands (the CreatedOnlySlice fact stays
// for any future row).

// RETIRED (MP signoff 2026-08-26, DT-024 E7): `soak_rcv_linePoolExclusive` — the law is
// PROVEN INDUCTIVE in receiver_pool_inductive.als (base + step + law, state-local; both
// scope gates green 2026-08-25), which supersedes the trace search this command never
// finished (UNKNOWN at 8d glucose / 12h gimsatul-8t). Its unit-scope sibling
// (receiver_pool_exclusive.als) retired with it.

// CREATED-ONLY SLICE (DT-023 Q-D / DT-024, closing pass 7c): reference-data version
// dynamics are proven WIDE in soak/tests/reference_data_dynamics — this root reads
// reference data only through the pin/liveness API, so each subject carries exactly its
// Create and no Update/Delete atoms inflate the census (the lemma-then-slice retune).
fact CreatedOnlySlice {
  ItemOcc in CreateItemOcc
  BaOcc in CreateBaOcc
  StaffOcc in CreateStaffOcc
}
