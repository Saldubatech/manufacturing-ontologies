module receiving/receiver/receiver_mock

/*
 * RECEIVER — MOCK (DT-017). Consumer UNIT roots open this file instead of
 * receiver_implementation: opening it IS assuming the module's published contract (a
 * module-level profile in the DT-012 sense). Never open together with
 * receiver_implementation in one root (lint-guarded).
 *
 * §8.5.3 mock rule: the lattice row `linePoolExclusiveWhileLive` rides `guarantees` — its
 * implementation-tier check is discharged in this module's unit suite IN THE SAME CHANGE
 * SET (the two-role pattern: the same law text is a CHECK against the implementation and,
 * through this file, a FACT in consumer universes).
 */

open receiving/receiver/receiver_contracts

fact ReceiverContractAssumed { guarantees }
