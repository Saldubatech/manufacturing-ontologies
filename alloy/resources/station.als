module resources/station

open meta/util   // Resource (for Equipment and ProcessingStation.associatedResource)

// Structural workstations / physical resources.
abstract sig Station {}
sig SinkStation   extends Station {}
sig SourceStation extends Station {}
sig ProcessingStation extends Station {
  associatedResource: one Resource
}

sig Equipment extends Resource {}

// (Subsigs of Station are already disjoint via `extends`; these explicit
//  disjointness facts are retained verbatim from the original model.)
fact StationDisjoint {
  no (SinkStation & SourceStation)
  no (SinkStation & ProcessingStation)
  no (SourceStation & ProcessingStation)
}
