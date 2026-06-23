module resources/job

open resources/item_type    // ItemType
open resources/kanban_card  // KanbanCard

// A Job — an aggregation of homogeneous Kanban cards formed at a source station.
sig Job {
  jobItemType: one ItemType,
  cards:       some KanbanCard
}

fact JobInvariants {
  // every job is homogeneous in ItemType
  all j: Job | all c: j.cards | c.itemType = j.jobItemType
  // a card belongs to at most one job
  all j1, j2: Job | j1 != j2 => no (j1.cards & j2.cards)
}
