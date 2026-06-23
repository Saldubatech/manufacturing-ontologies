module resources/kanban_card

open resources/item_type  // ItemType
open resources/loop       // Loop

// The 8-stage Kanban lifecycle (relocated; names kept — redesign aligns to the
// documented 9-state KanbanState + CardPrintState, DT-001.08).
abstract sig KanbanLifecycleState {}
one sig State1_AttachedAtSink,
        State2_ReleasedFromSink,
        State3_TransitingToSource,
        State4_ArrivedAtSource,
        State5_GroupedIntoJob,
        State6_InProcessAtSource,
        State7_CompletedAtSource,
        State8_TransitingToSink extends KanbanLifecycleState {}

sig KanbanCard {
  itemType:          one ItemType,
  belongsToLoop:     one Loop,
  var lifecycleState: one KanbanLifecycleState
}

// Card-vs-loop invariants (reference both KanbanCard and Loop → owned here).
fact CardLoopInvariants {
  all c: KanbanCard | c.belongsToLoop.capacityLimit >= 1
  all l: Loop | # {c: KanbanCard | c.belongsToLoop = l} <= l.capacityLimit
}
