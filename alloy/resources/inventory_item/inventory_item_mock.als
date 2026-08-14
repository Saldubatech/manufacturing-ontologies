module resources/inventory_item/inventory_item_mock

/*
 * INVENTORY ITEM — MOCK (DT-017). Consumer UNIT roots open this file instead of
 * inventory_item_implementation: it assumes the published contract as fact (opening IS
 * assuming — a module-level profile in the DT-012 sense), giving the consumer the observables'
 * laws WITHOUT the fifteen occurrence kinds, their guards, or the LOCF machinery in the
 * universe. Composition: `consumer_impl ∧ II_contract ⊨ consumer_contract` (unit root, here)
 * plus `II_impl ⊨ II_contract` (discharged in tests/unit/inventory_item.als) yields the
 * integration claim — scope-bounded, per the small-scope hypothesis applied compositionally.
 *
 * NEVER open this file together with inventory_item_implementation in one root (lint-guarded).
 * Every unit root opening this mock MUST carry a joint SAT `loads` witness — with the
 * implementation absent, over-constraint would otherwise pass silently as vacuity.
 */

open resources/inventory_item/inventory_item_contracts

fact InventoryItemContractAssumed { guarantees }
