module operations/demand/demand_mock

/*
 * DEMAND — MOCK (DT-017). Consumer UNIT roots (the future procurement/orders — DT-014 rung 3)
 * open this file instead of demand_implementation: opening it IS assuming the module's published
 * contract (a module-level profile in the DT-012 sense). Never open together with
 * demand_implementation in one root (lint-guarded).
 */

open operations/demand/demand_contracts

fact DemandContractAssumed { guarantees }
