module meta/time/instant

/*
 * The bare DOMAIN-TIME AXIS: `Instant` with an intrinsic total order, its comparison vocabulary,
 * and the closed `TimeInterval`. Split out of `meta/time/time` (2026-07-02, DT-006 domain build) so
 * that modules needing only the axis — notably `meta/occurrence`, and through it EVERY action/log
 * module — do not drag in the ARITY-4 elapsed-time metric (`TimeMetric.span`): Kodkod cannot
 * represent an arity-4 relation once the universe exceeds ~215 atoms (2^31 tuple indices), and
 * domain occurrence-log universes routinely do. Calendar periods and the metric stay in
 * `meta/time/time` (which opens this).
 *
 * The order is a global FACT (not a premise): a finite total order is always satisfiable, and
 * anyone opening the axis wants time ordered (cost localized by the module boundary).
 */

/** Instant — a point in time (opaque); `lte` is the ≤ relation (a.lte = the instants ≥ a). */
sig Instant { lte: set Instant }

fact InstantIsTotalOrder {
  all a: Instant | a in a.lte                                            // reflexive
  all a, b: Instant | (b in a.lte and a in b.lte) implies a = b          // antisymmetric
  all a, b, c: Instant | (b in a.lte and c in b.lte) implies c in a.lte  // transitive
  all a, b: Instant | b in a.lte or a in b.lte                           // total
}

/** atOrBefore — a ≤ b. */
pred atOrBefore[a, b: Instant] { b in a.lte }
/** earlierThan — a < b (strictly earlier). NB: `before` is a reserved LTL keyword in Alloy 6. */
pred earlierThan[a, b: Instant] { b in a.lte and a != b }

/** earliest — the minimum of a set of instants (`lone`; present iff `ts` is non-empty). */
fun earliest[ts: set Instant]: lone Instant { { t: ts | all u: ts | u in t.lte } }
/** latest — the maximum of a set of instants (`lone`). */
fun latest[ts: set Instant]: lone Instant { { t: ts | all u: ts | t in u.lte } }

/** TimeInterval — a closed window [from, to] (from ≤ to). */
sig TimeInterval { from: one Instant, to: one Instant }
fact IntervalWellFormed { all i: TimeInterval | atOrBefore[i.from, i.to] }

/** within — instant `t` falls inside interval `i` (inclusive of both ends). */
pred within[t: Instant, i: TimeInterval] { atOrBefore[i.from, t] and atOrBefore[t, i.to] }
