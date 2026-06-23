module meta/x731_state/state

/*
 * ITU-T X.731 three-vector resource state model + the abstract Resource bearer.
 * Relocated verbatim from meta/util.als (names unchanged — see DT-001.08 for the
 * redesign onto meta/kernel). This is the first file of the meta/x731_state package,
 * which will grow to hold state transitions, additional state attributes, and their
 * tests as the state machinery gains sophistication.
 */

-- X.731 Operational State (physical health / capability)
abstract sig OperationalState {}
one sig Enabled, Disabled extends OperationalState {}

-- X.731 Usage State (process loading)
abstract sig UsageState {}
one sig Idle, Active, Busy extends UsageState {}

-- X.731 Administrative State (policy control)
abstract sig AdministrativeState {}
one sig Unlocked, Locked, ShuttingDown extends AdministrativeState {}

-- Any asset carrying an X.731 state configuration. Concrete resources
-- (Equipment, Personnel, Loop) extend this in the resources/ domain.
abstract sig Resource {
  var operationalState:    one OperationalState,
  var usageState:          one UsageState,
  var administrativeState: one AdministrativeState
}

fact ResourceStateInvariants {
  all r: Resource | r.operationalState   = Disabled => r.usageState = Idle
  all r: Resource | r.administrativeState = Locked  => r.usageState = Idle
}

-- Checkable form of the interlock (command lives in meta/x731_state/tests/state.als).
assert X731Consistency {
  all r: Resource | r.operationalState = Disabled => r.usageState = Idle
}
