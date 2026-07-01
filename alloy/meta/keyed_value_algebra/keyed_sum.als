module meta/keyed_value_algebra/keyed_sum[Node]

/*
 * Σ of keyed values along a linear order — the fold the keyed monoid lacks (`keyed_monoid` gives only the
 * BINARY `add`). PARAMETERIZED over the carrier `Node`: each `open keyed_sum[X]` gets its OWN fold state,
 * so multiple independent folds coexist in one model (the measurement temporal SUM over `Measurement`,
 * the cross-sectional Σ over items, the UoM conversion collapse over unit-contributions, …).
 *
 * The opener supplies, via facts on `Fold`: `val` (each node's normal-form keyed value `univ -> lone
 * Scalar`) and `earlier` (the linear chain order). `cum` (the running total) is then pinned by the
 * recurrence below; read `chainSum` / `rangeSum`. `val`/`cum` are RAW MAP slices — no value-object
 * atom-existence trap. The chain order is arbitrary for the result (add is commutative + associative
 * under `ringAxioms`), so a caller imposes any convenient order (time, eId, …).
 *
 * SEE ALSO: meta/keyed_value_algebra/keyed_monoid; DT-008 (measurement SUM); DT-009 (UoM collapse); G2.
 */

open meta/keyed_value_algebra/keyed_monoid   // Scalar, add, negate, zero, nf, isZero, ringAxioms

/** Fold — the per-instantiation fold state over `Node`: the chain predecessor `earlier`, each node's
    value `val`, and the running total `cum` (head..node). The opener pins `earlier`/`val`; `cum` is
    derived by `RunningSumDef`. */
one sig Fold {
  earlier: Node -> lone Node,
  val:     Node -> univ -> lone Scalar,
  cum:     Node -> univ -> lone Scalar
}

/** Chains are acyclic, linear (≤1 predecessor via `lone`, ≤1 successor here), normal-form values. */
fact ChainWellFormed {
  no n: Node | n in n.^(Fold.earlier)          // acyclic
  all p: Node | lone (Fold.earlier).p          // ≤ 1 successor (linear chains, not trees)
  all n: Node | nf[Fold.val[n]]                // each value in normal form
}

/** The running total is the fold of `add` along the chain — base = `val` at the head. */
fact RunningSumDef {
  all n: Node |
    (no Fold.earlier[n] => Fold.cum[n] = Fold.val[n]
                         else Fold.cum[n] = add[Fold.cum[Fold.earlier[n]], Fold.val[n]])
}

/** head / last — the endpoints of `n`'s chain. */
fun headSum[n: Node]: one Node { { x: n.*(Fold.earlier) | no Fold.earlier[x] } }
fun lastSum[n: Node]: one Node { { x: Node | n in x.*(Fold.earlier) and no (Fold.earlier).x } }

/** chainSum — Σ of the WHOLE chain containing `n` (= the running total at its last node). */
fun chainSum[n: Node]: univ -> lone Scalar { Fold.cum[lastSum[n]] }

/** rangeSum — Σ of the sub-chain from `lo` to `hi` inclusive (caller ensures `lo` ≤ `hi` in one chain):
    telescoping `cum[hi] − cum[just-before-lo]`. */
fun rangeSum[lo, hi: Node]: univ -> lone Scalar {
  some Fold.earlier[lo] => add[Fold.cum[hi], negate[Fold.cum[Fold.earlier[lo]]]] else Fold.cum[hi]
}
