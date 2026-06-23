module kanban_sim/tests/kanban

open kanban_sim/x731_state
open kanban_sim/station
open kanban_sim/operator
open kanban_sim/loop
open kanban_sim/kanban_card
open kanban_sim/job
open kanban_sim/inventory_item

/*
 * Kanban behavioral suite — transition operations + simulation run.
 * Relocated verbatim from the old kanban.als (RELOCATION; predicate and command
 * names unchanged). Operations span resources modules + meta/x731_state, so they
 * live in this domain test root rather than in any single library module.
 */

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
