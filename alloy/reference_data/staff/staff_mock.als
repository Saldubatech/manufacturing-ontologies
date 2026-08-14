module reference_data/staff/staff_mock

/*
 * STAFF — MOCK (DT-017). Consumer UNIT roots open this file instead of the implementation:
 * assumes the published contract as fact. MINIMAL-LOG discipline (DT-023 Q-D): the mock
 * forces no occurrences — a consumer witness gives each referenced member exactly the
 * Creates it needs. NEVER open together with staff_implementation (lint-guarded).
 */

open reference_data/staff/staff_contracts

fact StaffContractAssumed { guarantees }
