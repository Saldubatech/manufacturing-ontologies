module KanbanManufacturingSystem

open resource   -- Resource sig + X.731 state vectors (operational / usage / administrative)

/*
================================================================================
1. STATIC SIGNATURES & VALUE PARTITIONS (The Data Schema)
================================================================================
*/

-- Abstract structural types
abstract sig ItemType {}

-- NOTE: Resource and the X.731 state vectors (OperationalState, UsageState,
-- AdministrativeState) now live in resource.als (opened above).

-- The 8-Stage Kanban Lifecycle Vector
abstract sig KanbanLifecycleState {}
one sig State1_AttachedAtSink,
        State2_ReleasedFromSink,
        State3_TransitingToSource,
        State4_ArrivedAtSource,
        State5_GroupedIntoJob,
        State6_InProcessAtSource,
        State7_CompletedAtSource,
        State8_TransitingToSink extends KanbanLifecycleState {}

-- Structural Workstations
abstract sig Station {}
sig SinkStation extends Station {}
sig SourceStation extends Station {}

-- Resource Hierarchies (Resource + X.731 state vectors are defined in resource.als)
sig Equipment extends Resource {}
sig Personnel extends Resource {}

sig ProcessingStation extends Station {
  associatedResource: one Resource
}

sig Loop extends Resource {
  source: one SourceStation,
  sink: one SinkStation,
  elements: some Resource,
  capacityLimit: one Int
} {
  capacityLimit > 0
  this not in elements
}

-- Control Tokens and Aggregations
sig KanbanCard {
  itemType: one ItemType,
  belongsToLoop: one Loop,
  var lifecycleState: one KanbanLifecycleState
}

sig Job {
  jobItemType: one ItemType,
  cards: some KanbanCard
}

-- Physical Material Batches
sig InventoryLot {
  lotItemType: one ItemType,
  var currentStation: one Station
}

/*
================================================================================
2. FACT CONSTRAINTS (Invariants Enforced Across All Valid States)
================================================================================
*/

fact StructuralInvariants {
  -- Disjoint stations
  -- no (SinkStation & SourceStation)
  -- no (SinkStation & ProcessingStation)
  -- no (SourceStation & ProcessingStation)
  
  -- Every card belongs to a loop matching its lifecycle bounds
  all c: KanbanCard | c.belongsToLoop.capacityLimit >= 1

  -- Loop decomposition constraints
  all l: Loop | no (l & l.elements)
  
  -- Every Job must be homogenous in terms of ItemType
  all j: Job | all c: j.cards | c.itemType = j.jobItemType
  
  -- Prevent cards from belonging to multiple overlapping active jobs simultaneously
  all var_job1, var_job2: Job | var_job1 != var_job2 => no (var_job1.cards & var_job2.cards)
}

-- Resource-level X.731 interlocks live in resource.als (ResourceStateInvariants).
-- This keeps only the Loop-level aggregation rule, which needs Loop + elements.
fact LoopStateInvariants {
  -- If a loop is disabled, its component resources drop to Idle.
  all l: Loop | l.operationalState = Disabled => (all e: l.elements | e.usageState = Idle)
}

fact LoopCapacityLimits {
  -- The number of active Kanban cards circulating inside a loop cannot exceed its authorized WIP cap
  all l: Loop | # {c: KanbanCard | c.belongsToLoop = l} <= l.capacityLimit
}

/*
================================================================================
3. STATE TRANSITIONS (Dynamic Behavior Operations)
================================================================================
*/

-- Op 1: Downstream Consumption (Card release at Sink)
pred releaseCardFromSink [c: KanbanCard, lot: InventoryLot] {
  -- Pre-conditions
  c.lifecycleState = State1_AttachedAtSink
  lot.lotItemType = c.itemType
  lot.currentStation = c.belongsToLoop.sink

  -- Post-conditions
  c.lifecycleState' = State2_ReleasedFromSink
  lot.currentStation' != c.belongsToLoop.sink -- Lot moves away into consumption zone

  -- Frame conditions
  all other_c: KanbanCard - c | other_c.lifecycleState' = other_c.lifecycleState
  all other_r: Resource | other_r.operationalState' = other_r.operationalState
  all other_r: Resource | other_r.usageState' = other_r.usageState
  all other_r: Resource | other_r.administrativeState' = other_r.administrativeState
}

-- Op 2: Complete Route Transit Back to Source Input Queue
pred cardArrivesAtSource [c: KanbanCard] {
  -- Pre-conditions
  c.lifecycleState = State3_TransitingToSource

  -- Post-conditions
  c.lifecycleState' = State4_ArrivedAtSource

  -- Frame conditions
  all other_c: KanbanCard - c | other_c.lifecycleState' = other_c.lifecycleState
  all other_r: Resource | other_r.operationalState' = other_r.operationalState
  all other_r: Resource | other_r.usageState' = other_r.usageState
  all other_r: Resource | other_r.administrativeState' = other_r.administrativeState
}

-- Op 3: Combinatorial Job Grouping at Source Station
pred formProductionJob [src: SourceStation, j: Job] {
  -- Pre-conditions
  all c: j.cards | c.lifecycleState = State4_ArrivedAtSource
  all c: j.cards | c.belongsToLoop.source = src

  -- Post-conditions
  all c: j.cards | c.lifecycleState' = State5_GroupedIntoJob

  -- Frame conditions
  all other_c: KanbanCard - j.cards | other_c.lifecycleState' = other_c.lifecycleState
  all other_r: Resource | other_r.operationalState' = other_r.operationalState
  all other_r: Resource | other_r.usageState' = other_r.usageState
  all other_r: Resource | other_r.administrativeState' = other_r.administrativeState
}

-- Op 4: Job Execution Start (Decoupled X.731 Resource State Interlocking)
pred startJobExecution [j: Job, pstat: ProcessingStation] {
  -- Pre-conditions
  let res = pstat.associatedResource {
    res.operationalState = Enabled
    res.administrativeState = Unlocked
    res.usageState = Idle
    all c: j.cards | c.lifecycleState = State5_GroupedIntoJob
    
    -- Post-conditions
    res.usageState' = Busy
    all c: j.cards | c.lifecycleState' = State6_InProcessAtSource
  }

  -- Frame conditions
  all other_c: KanbanCard - j.cards | other_c.lifecycleState' = other_c.lifecycleState
  all other_r: Resource - pstat.associatedResource | other_r.usageState' = other_r.usageState
  all other_r: Resource | other_r.operationalState' = other_r.operationalState
  all other_r: Resource | other_r.administrativeState' = other_r.administrativeState
}

-- Op 5: Machine Fault Triggering X.731 Dependency Override
pred triggerMachineFault [res: Resource] {
  -- Pre-conditions
  res.operationalState = Enabled

  -- Post-conditions
  res.operationalState' = Disabled
  res.usageState' = Idle -- Enforced correction by state interlock pattern

  -- Frame conditions
  all other_r: Resource - res | other_r.operationalState' = other_r.operationalState
  all other_r: Resource - res | other_r.usageState' = other_r.usageState
  all other_r: Resource | other_r.administrativeState' = other_r.administrativeState
  all c: KanbanCard | c.lifecycleState' = c.lifecycleState
}

/*
================================================================================
4. LIVENESS, INITIAL STATES, AND SYSTEM INITIALIZATION
================================================================================
*/

pred init [s: KanbanCard] {
  all c: KanbanCard | c.lifecycleState = State1_AttachedAtSink
  all r: Resource | r.operationalState = Enabled
  all r: Resource | r.usageState = Idle
  all r: Resource | r.administrativeState = Unlocked
}

-- The resource X.731 consistency assertion now lives in resource.als (pattern (a):
-- each module self-tests). Open resource.als to run `check X731Consistency`.

-- Generate a complete simulation trace showing valid operations
pred showSimulation {
  some c: KanbanCard, lot: InventoryLot, j: Job, pstat: ProcessingStation |
    releaseCardFromSink[c, lot] or cardArrivesAtSource[c] or formProductionJob[c.belongsToLoop.source, j] or startJobExecution[j, pstat]
}
run showSimulation for 4 but 8 Int
