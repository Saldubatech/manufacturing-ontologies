module reference_data/item/item_mock

/*
 * ITEM — MOCK (DT-017). Consumer UNIT roots open this file instead of item_implementation:
 * it assumes the module's published contract as fact — opening it IS assuming (a module-level
 * profile in the DT-012 sense). A unit root proving `consumer_impl ∧ item_contract ⊨ goal`
 * composes with the integration evidence that the real item satisfies the same contract.
 *
 * Since the DT-023 cut 7a log conversion the mock is NO LONGER textually the implementation:
 * it assumes the content axioms + the lifecycle/chaining laws WITHOUT the guard/effect
 * machinery. MINIMAL-LOG discipline (DT-023 Q-D): the mock forces no occurrences — a
 * consumer witness gives each referenced item exactly the Creates it needs (the
 * reference-data-first fixture convention), and pinning/liveness reads work off those.
 *
 * NEVER open this file together with item_implementation in one root (lint-guarded).
 */

open reference_data/item/item_contracts

fact ItemContractAssumed { guarantees }
