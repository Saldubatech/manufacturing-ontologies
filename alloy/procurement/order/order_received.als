module procurement/order/order_received

/*
 * ORDER — the CONFINED accumulate-completeness reading of `sReceived` (the kit's
 * denormalized-observables obligation (a): the stored value EQUALS what a full recompute over
 * the log would produce). Unlike demand_reset's ResetQtySum this is NOT an extra effect — it is
 * a THEOREM of receiptAccrues (pairwise +=) + line genesis (the keyed zero) + every other
 * effect's framing. It is stated CASE-WISE (0/1/2 committed postings — exact) and discharged
 * ONLY in its dedicated root (tests/unit/order_received.als): the general fold cannot ride this
 * cone (the demand_reset arity-4 finding applies a fortiori — the order cone is heavier). The
 * runtime computes the real Σ without ceilings; the law probe's self-heal recomputes through
 * the drill-down. Solver-budget confinement, not a domain rule.
 */

open procurement/order/order_implementation

/** committedReceiptsUpTo — the line's committed receipt postings at-or-before `t`. */
fun committedReceiptsUpTo[l: OrderLine, t: Tick]: set RecordReceiptOcc {
  { r: RecordReceiptOcc | committed[r] and r.subject = l and notAfter[r.tick, t] }
}

/** receivedIsAccumulatedAt — the stored `sReceived` equals the Σ of committed postings
    (case-wise: 0/1/2 exact; the dedicated root's scopes stay ≤ 2 postings per line). */
pred receivedIsAccumulatedAt[l: OrderLine, t: Tick] {
  startedLineAt[l, t] implies {
    let rs = committedReceiptsUpTo[l, t] | {
      (no rs)   implies no qtyMap[lineStateAt[l, t].sReceived]
      (one rs)  implies qtyMap[lineStateAt[l, t].sReceived] = qtyMap[rs.qty]
      (#rs = 2) implies (some disj r1, r2: rs |
        qtyMap[lineStateAt[l, t].sReceived] = add[qtyMap[r1.qty], qtyMap[r2.qty]])
    }
  }
}
