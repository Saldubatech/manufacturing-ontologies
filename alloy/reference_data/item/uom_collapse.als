module reference_data/item/uom_collapse

/*
 * MULTI-UNIT UoM collapse (DT-009): `collapse(sch, q) = { each ↦ Σ_u q[u] · factor[u] }` — the total of a
 * MultiQuantity `q` expressed in the canonical `each` unit, under a tracked Item's `UomScheme`. This is
 * the conversion HOMOMORPHISM that upgrades the partial keyed order / zero-check / capacity to TOTAL for
 * inventory-tracked items. The single-unit base case is `uom/toEach`; here we fold the per-unit products
 * across all of `q`'s units with the keyed Σ.
 *
 * HOW: reify one CONTRIBUTION NODE per (scheme, quantity, unit-in-support); each node carries the
 * single-key value `{ each ↦ q[u]·factor[u] }`. We then instantiate the parameterized `keyed_sum[Node]`
 * over `ConvNode`, chaining each (scheme, quantity) group into ONE linear chain, so `chainSum`/`Fold.cum`
 * folds the group's contributions into the `each` total. The chain ORDER is arbitrary — `add` is
 * commutative + associative under `ringAxioms` — so the result is order-independent.
 *
 * SEE ALSO: reference_data/item/uom (UomScheme, Each, toEach); meta/keyed_value_algebra/keyed_sum; DT-009.
 */

open shared/values                                    // Quantity, Unit
open meta/scalar/scalar                             // Scalar, SZero, SOne, splus, smul, ringAxioms
open reference_data/item/uom                        // UomScheme, Each, toEach, units
open meta/keyed_value_algebra/keyed_sum[ConvNode]   // Fold, add, zero, nf, chainSum (forward-refs ConvNode)

/** ConvNode — one per (scheme, quantity, unit-in-support): the contribution of unit `cunit` of quantity
    `cquant` under scheme `csch`. Its fold value is the single-key map `{ each ↦ cquant[cunit]·factor }`. */
sig ConvNode {
  csch:   one UomScheme,
  cunit:  one Unit,
  cquant: one Quantity
}

fact ConvNodesWF {
  all n: ConvNode {
    n.cunit in n.cquant.byUnit.Scalar          // the unit is in the quantity's support
    some n.csch.factor[n.cunit]                // the unit is configured in the scheme
  }
  // at most one node per (scheme, quantity, unit)
  all disj a, b: ConvNode | not (a.csch = b.csch and a.cquant = b.cquant and a.cunit = b.cunit)
  // a present group covers EXACTLY its quantity's support — so a collapse, when reified, is complete
  all n: ConvNode |
    { m: ConvNode | m.csch = n.csch and m.cquant = n.cquant }.cunit = n.cquant.byUnit.Scalar
}

fact FoldFromConv {
  // node value = the per-unit `each`-contribution, zero-dropped to stay in normal form
  all n: ConvNode |
    Fold.val[n] = { k: Unit, v: Scalar |
      k = Each and v = (n.cquant.byUnit[n.cunit]).smul[n.csch.factor[n.cunit]] and v != SZero }
  // the fold chain links nodes only WITHIN a (scheme, quantity) group
  all n: ConvNode | some Fold.earlier[n] =>
    (Fold.earlier[n].csch = n.csch and Fold.earlier[n].cquant = n.cquant)
  // each group is a single CONNECTED chain, so its `chainSum` totals the whole support
  all n: ConvNode |
    let g = { m: ConvNode | m.csch = n.csch and m.cquant = n.cquant } |
      all disj a, b: g | (a in b.^(Fold.earlier) or b in a.^(Fold.earlier))
}

/** hasGroup — the (scheme, quantity) collapse is reified (a contribution node exists). With `ConvNodesWF`
    this implies the group covers `q`'s full support. */
pred hasGroup[sch: UomScheme, q: Quantity] { some n: ConvNode | n.csch = sch and n.cquant = q }

/** collapseTail — the group's chain tail (no successor); exists iff the group is non-empty. */
fun collapseTail[sch: UomScheme, q: Quantity]: lone ConvNode {
  { x: ConvNode | x.csch = sch and x.cquant = q and no (Fold.earlier).x }
}

/** collapse — `q` totalled into the canonical `each` unit under `sch`: `{ each ↦ Σ_u q[u]·factor[u] }`
    (the empty map `zero` when no contribution group is reified). Single-key by construction. */
fun collapse[sch: UomScheme, q: Quantity]: univ -> lone Scalar {
  let g = { n: ConvNode | n.csch = sch and n.cquant = q } |
    (no g => zero else Fold.cum[collapseTail[sch, q]])
}
