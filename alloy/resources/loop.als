module resources/loop

open meta/x731_state/state          // Resource, state vectors
open resources/station  // SourceStation, SinkStation

// A Kanban Loop: a composite resource linking a source to a sink station.
sig Loop extends Resource {
  source:        one SourceStation,
  sink:          one SinkStation,
  elements:      some Resource,
  capacityLimit: one Int
} {
  capacityLimit > 0
  this not in elements
}

// Loop-level invariants (no card references here — those live in kanban_card.als).
fact LoopStructuralInvariants {
  all l: Loop | no (l & l.elements)
}

fact LoopStateInvariants {
  all l: Loop | l.operationalState = Disabled => (all e: l.elements | e.usageState = Idle)
}
