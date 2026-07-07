module resources/processing_network/processing_network_mock

/*
 * PROCESSING NETWORK — MOCK (DT-017). Consumer UNIT roots open this instead of the
 * implementation: opening it IS assuming the published contract. Never open together with
 * processing_network_implementation in one root (lint-guarded). Textually identical to the
 * implementation today (static-module degeneracy) — rely only on the CONTRACT.
 */

open resources/processing_network/processing_network_contracts

fact ProcessingNetworkContractAssumed { guarantees }
