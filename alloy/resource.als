module resource

/*
================================================================================
Resource concern — the Resource signature and the ITU-T X.731 three-vector
state model (operational / usage / administrative). Opened by kanban.als.
================================================================================
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

-- Any asset/device/human/system carrying an X.731 state configuration.
-- Subtypes (Equipment, Personnel, Loop) are defined in the opening module.
abstract sig Resource {
  var operationalState:    one OperationalState,
  var usageState:          one UsageState,
  var administrativeState: one AdministrativeState
}

/*
================================================================================
Resource-level invariants + self-test (the X.731 state interlock).
Pattern (a): this module carries its own assertions/commands, so it can be
analysed standalone — open resource.als and Execute to check it in isolation.
================================================================================
*/

-- A resource that is physically disabled, or administratively locked, cannot be
-- loaded with work: its usage state must be Idle.
fact ResourceStateInvariants {
  all r: Resource | r.operationalState   = Disabled => r.usageState = Idle
  all r: Resource | r.administrativeState = Locked  => r.usageState = Idle
}

-- The interlock above never produces an invalid combination.
assert X731Consistency {
  all r: Resource | r.operationalState = Disabled => r.usageState = Idle
}
check X731Consistency for 5
