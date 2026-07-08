module procurement/order/order_mock

/*
 * ORDER — MOCK (DT-017). Consumer UNIT roots (the future receiving module — DT-014 rung 4)
 * open this file instead of order_implementation: opening it IS assuming the module's published
 * contract (a module-level profile in the DT-012 sense). Never open together with
 * order_implementation in one root (lint-guarded).
 */

open procurement/order/order_contracts

fact OrderContractAssumed { guarantees }
