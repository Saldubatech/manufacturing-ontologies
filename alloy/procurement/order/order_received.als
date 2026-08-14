module procurement/order/order_received

/*
 * ORDER — the CONFINED accumulate-completeness reading of `sReceived` (the kit's
 * denormalized-observables obligation (a): the stored value EQUALS what a full recompute over
 * the log would produce). Unlike demand_reset's ResetQtySum this is NOT an extra effect — it is
 * a THEOREM of receiptAccrues (pairwise +=) + receiptReverses (pairwise −=, cut 9) + line
 * genesis (the keyed zero) + every other effect's framing. It is stated CASE-WISE (0/1/2 committed postings — exact) and discharged
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
/** committedReversalsUpTo — the line's committed COMPENSATING postings at-or-before `t`
    (F9b, cut 9). */
fun committedReversalsUpTo[l: OrderLine, t: Tick]: set ReverseReceiptOcc {
  { v: ReverseReceiptOcc | committed[v] and v.subject = l and notAfter[v.tick, t] }
}

/** receivedIsAccumulatedAt — the stored `sReceived` equals the Σ of committed postings MINUS
    the Σ of committed reversals (case-wise exact over the root's budget: ≤ 2 receipts, ≤ 1
    reversal per line; cut 9 adds the reversal cases — including the reversal-BEFORE-accrual
    window, where the stored value reads negative). */
pred receivedIsAccumulatedAt[l: OrderLine, t: Tick] {
  startedLineAt[l, t] implies {
    let rs = committedReceiptsUpTo[l, t], vs = committedReversalsUpTo[l, t] | {
      (no rs and no vs)   implies no qtyMap[lineStateAt[l, t].sReceived]
      (one rs and no vs)  implies qtyMap[lineStateAt[l, t].sReceived] = qtyMap[rs.qty]
      (#rs = 2 and no vs) implies (some disj r1, r2: rs |
        qtyMap[lineStateAt[l, t].sReceived] = add[qtyMap[r1.qty], qtyMap[r2.qty]])
      (one rs and one vs) implies
        qtyMap[lineStateAt[l, t].sReceived] = add[qtyMap[rs.qty], negate[qtyMap[vs.qty]]]
      (no rs and one vs)  implies
        qtyMap[lineStateAt[l, t].sReceived] = negate[qtyMap[vs.qty]]
    }
  }
}
