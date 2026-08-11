module procurement/order/tests/unit/order_received

open procurement/order/order_received

/*
 * DEDICATED root for the sReceived ACCUMULATE reading (the kit's denormalized-observables
 * obligation (a)) — the ONLY root that opens order_received.als. Unlike demand_reset's fact,
 * receivedIsAccumulatedAt is a THEOREM here (receiptAccrues + genesis-zero + framing), so this
 * root CHECKS it (case-wise 0/1/2 postings — scopes pin RecordReceiptOcc ≤ 2) and witnesses
 * both ends. The kanban print machine rides the cone: pins as everywhere.
 */

// The theorem: the stored value equals the recompute, for every line at every tick (≤2 postings).
assert unit_ordr_receivedIsAccumulated {
  all l: OrderLine, t: Tick | receivedIsAccumulatedAt[l, t]
}
check unit_ordr_receivedIsAccumulated for 5 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 2 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      2 RecordReceiptOcc, 8 Quantity, 2 Note expect 0

// Witness, empty end: a started line with no postings reads the keyed zero.
run unit_ordr_zeroBeforeAnyPosting {
  some a: AddLineOcc, t: Tick | {
    committed[a] and notAfter[a.tick, t]
    no r: RecordReceiptOcc | committed[r]
    no qtyMap[lineStateAt[a.subject, t].sReceived]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      8 EntityId, 8 Snapshot, 2 Note expect 1

// Witness, accumulating end: two committed postings; the stored value is their pairwise sum.
run unit_ordr_twoPostingsAccumulate {
  some disj r1, r2: RecordReceiptOcc, t: Tick | {
    committed[r1] and committed[r2]
    r1.subject = r2.subject
    precedes[r1.tick, r2.tick] and notAfter[r2.tick, t]
    qtyMap[lineStateAt[r1.subject, t].sReceived] = add[qtyMap[r1.qty], qtyMap[r2.qty]]
  }
} for 6 but 5 Int, 3 Scalar, 5 State, 8 Signal, 8 Transition, 1 StateMachine, 0 Guard,
      1 Order, 1 OrderLine, 0 DemandItem, 0 CardCycle, 0 KanbanCard, 0 InventoryItem, 0 InventoryPool, 0 Station,
      9 Tick, 9 EntityId, 10 Snapshot, 5 Quantity, 2 Note expect 1
