module reference_data/item/item_mock

/*
 * ITEM — MOCK (DT-017). Consumer UNIT roots open this file instead of item_implementation:
 * it assumes the module's published contract as fact — opening it IS assuming (a module-level
 * profile in the DT-012 sense). A unit root proving `consumer_impl ∧ item_contract ⊨ goal`
 * composes with the integration evidence that the real item satisfies the same contract.
 *
 * NEVER open this file together with item_implementation in one root (mock+real of the same
 * module in one universe is meaningless — lint-guarded). For this static module the mock is
 * textually identical to the implementation (see the degeneracy note there); rely only on the
 * CONTRACT, not on that coincidence.
 */

open reference_data/item/item_contracts

fact ItemContractAssumed { guarantees }
