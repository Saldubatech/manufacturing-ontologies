module reference_data/business_affiliate/business_affiliate_mock

/*
 * BUSINESS AFFILIATE — MOCK (DT-017). Consumer UNIT roots open this file instead of the
 * implementation: it assumes the module's published contract as fact — opening it IS assuming.
 *
 * Since the DT-023 cut 7b log conversion the mock is NO LONGER textually the implementation:
 * it assumes the content axiom + the lifecycle/chaining laws WITHOUT the guard/effect
 * machinery. MINIMAL-LOG discipline (DT-023 Q-D): the mock forces no occurrences — a consumer
 * witness gives each referenced affiliate exactly the Creates it needs (the
 * reference-data-first fixture convention), and pinning/liveness reads work off those.
 *
 * NEVER open this file together with business_affiliate_implementation in one root
 * (lint-guarded).
 */

open reference_data/business_affiliate/business_affiliate_contracts

fact BaContractAssumed { guarantees }
