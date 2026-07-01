module meta/examples/ex09_parallel_regions

/*
 * PATTERN:  Orthogonal / parallel state regions on one host + a cross-region interlock.
 * UML:      State machine with orthogonal regions (AND-states).
 * FP:       A product of independent state values with a cross-field invariant.
 * USE WHEN:  An entity runs several independent lifecycles at once.
 * AVOID:     Encoding the cross product as one flat enum (combinatorial blow-up;
 *            the interlock becomes unstatable).
 * SEE ALSO:  meta/state_machine/machine.als; meta/x731_state/state.als (real use, X.731).
 *
 * A Room has three regions: occupancy ∥ housekeeping ∥ maintenance — each a reified
 * StateMachine — plus the interlock "out-of-service ⇒ not occupied" (the neutral twin
 * of X.731's "disabled ⇒ idle"). Multi-region = several state fields, one per machine.
 */

/*
  Orthogonal regions at a glance — preview this block with the VS Code PlantUML plugin
  (cursor inside, "PlantUML: Preview Current Diagram"):

@startuml
state Room {
  state Occupancy {
    [*] --> VACANT
    VACANT --> RESERVED : RESERVE
    RESERVED --> OCCUPIED : CHECK_IN
    OCCUPIED --> VACANT : CHECK_OUT
  }
  --
  state Housekeeping {
    [*] --> CLEAN
    CLEAN --> DIRTY : SOIL
    INSPECTED --> DIRTY : SOIL
    DIRTY --> CLEAN : CLEAN_UP
    CLEAN --> INSPECTED : INSPECT
  }
  --
  state Maintenance {
    [*] --> IN_SERVICE
    IN_SERVICE --> OUT_OF_SERVICE : BLOCK
    OUT_OF_SERVICE --> IN_SERVICE : RELEASE
  }
}
note bottom of Room #white : //{ maintenance = OUT_OF_SERVICE implies occupancy != OCCUPIED }//
@enduml
*/

open meta/state_machine/machine

// --- Region 1: occupancy ----------------------------------------------------
abstract sig Occupancy extends State {}
one sig VACANT, RESERVED, OCCUPIED extends Occupancy {}
abstract sig OccupancySignal extends Signal {}
one sig RESERVE, CHECK_IN, CHECK_OUT extends OccupancySignal {}
one sig OccupancyMachine extends StateMachine {}
abstract sig OccTransition extends Transition {}
one sig Occ_reserve  extends OccTransition {} { from = VACANT   and on = RESERVE   and to = RESERVED }
one sig Occ_checkin  extends OccTransition {} { from = RESERVED and on = CHECK_IN  and to = OCCUPIED }
one sig Occ_checkout extends OccTransition {} { from = OCCUPIED and on = CHECK_OUT and to = VACANT }
fact OccupancyMachineDef {
  OccupancyMachine.states = Occupancy and OccupancyMachine.signals = OccupancySignal
  OccupancyMachine.start = VACANT and OccupancyMachine.transitions = OccTransition
  all t: OccTransition | no t.guard
}

// --- Region 2: housekeeping -------------------------------------------------
abstract sig Housekeeping extends State {}
one sig CLEAN, DIRTY, INSPECTED extends Housekeeping {}
abstract sig HousekeepingSignal extends Signal {}
one sig SOIL, CLEAN_UP, INSPECT extends HousekeepingSignal {}
one sig HousekeepingMachine extends StateMachine {}
abstract sig HkTransition extends Transition {}
one sig Hk_soil    extends HkTransition {} { from = CLEAN + INSPECTED and on = SOIL     and to = DIRTY }
one sig Hk_cleanup extends HkTransition {} { from = DIRTY             and on = CLEAN_UP and to = CLEAN }
one sig Hk_inspect extends HkTransition {} { from = CLEAN             and on = INSPECT  and to = INSPECTED }
fact HousekeepingMachineDef {
  HousekeepingMachine.states = Housekeeping and HousekeepingMachine.signals = HousekeepingSignal
  HousekeepingMachine.start = CLEAN and HousekeepingMachine.transitions = HkTransition
  all t: HkTransition | no t.guard
}

// --- Region 3: maintenance --------------------------------------------------
abstract sig Maintenance extends State {}
one sig IN_SERVICE, OUT_OF_SERVICE extends Maintenance {}
abstract sig MaintenanceSignal extends Signal {}
one sig BLOCK, RELEASE extends MaintenanceSignal {}
one sig MaintenanceMachine extends StateMachine {}
abstract sig MtTransition extends Transition {}
one sig Mt_block   extends MtTransition {} { from = IN_SERVICE     and on = BLOCK   and to = OUT_OF_SERVICE }
one sig Mt_release extends MtTransition {} { from = OUT_OF_SERVICE and on = RELEASE and to = IN_SERVICE }
fact MaintenanceMachineDef {
  MaintenanceMachine.states = Maintenance and MaintenanceMachine.signals = MaintenanceSignal
  MaintenanceMachine.start = IN_SERVICE and MaintenanceMachine.transitions = MtTransition
  all t: MtTransition | no t.guard
}

// --- The host occupies all three regions at once ----------------------------
sig Room {
  occupancy:    one Occupancy,
  housekeeping: one Housekeeping,
  maintenance:  one Maintenance
}

// Cross-region interlock (entry/exit conditions as invariants): an out-of-service
// room cannot be occupied. (The X.731 twin: disabled ⇒ idle.)
fact RoomInterlock {
  all r: Room | r.maintenance = OUT_OF_SERVICE => r.occupancy != OCCUPIED
}

// SAT: a room with a coherent combination of region states exists.
run someRoom { some Room }
  for 4 but 8 State, 8 Signal, 8 Transition, 3 StateMachine, 0 Guard expect 1

// UNSAT: the interlock forbids an out-of-service, occupied room.
run interlockForbidsBadRoom {
  some r: Room | r.maintenance = OUT_OF_SERVICE and r.occupancy = OCCUPIED
} for 4 but 8 State, 8 Signal, 8 Transition, 3 StateMachine, 0 Guard expect 0

// Each region machine is well-formed: every state reachable, every signal live.
check regionsWellFormed {
  allStatesReachable[OccupancyMachine]
  allStatesReachable[HousekeepingMachine]
  allStatesReachable[MaintenanceMachine]
  liveSignals[OccupancyMachine]
  liveSignals[HousekeepingMachine]
  liveSignals[MaintenanceMachine]
} for 4 but 8 State, 8 Signal, 8 Transition, 3 StateMachine, 0 Guard expect 0
