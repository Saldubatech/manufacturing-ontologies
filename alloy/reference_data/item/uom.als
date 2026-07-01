module reference_data/item/uom

/*
 * Units of measure & conversion for inventory-tracked Items (DT-009). An Item is inventory-tracked iff it
 * carries a `UomScheme`. The scheme is a STAR conversion to a canonical reference unit ALWAYS named
 * `each` (factor 1.0): every configured unit `u` has a factor `factor[u]` = how many `each` in one `u`.
 *
 * Unit names are normalized identifiers `[a-z][0-9_a-z-]*` (case-insensitive) — for both configured and
 * ad-hoc (non-tracked) units; modeled here as opaque `Unit` atoms (distinct atom = distinct canonical
 * name; Alloy has no strings/regex to enforce the lexical rule).
 *
 * Conversion factors are decimals strictly > 0 (including 0 < f < 1). The abstract `Scalar` carries
 * fractions; strict positivity is the intended domain (verifiable via `keyed_order.classify = POSITIVE`
 * under `orderAxioms`); structurally we require factors are non-zero.
 *
 * NB the MULTI-UNIT collapse `q → (total in each)` folds the per-unit products `q[u] · factor[u]` via the
 * keyed Σ; it lives in `reference_data/item/uom_collapse.als` (instantiates `keyed_sum[ConvNode]`). The
 * single-unit `toEach` below is its base case. See design/meta/keyed-value-algebra + DT-009.
 */

open meta/values            // Unit
open meta/scalar/scalar     // Scalar, SOne, SZero

/** Each — the canonical reference unit (factor 1.0), present in every tracked Item's scheme. */
one sig Each in Unit {}

/** UomScheme — a tracked Item's star conversion: `factor[u]` = number of `each` per one `u`. */
sig UomScheme {
  factor: Unit -> lone Scalar
}
fact UomSchemeWF {
  all s: UomScheme {
    some s.factor[Each]                          // each is always configured
    s.factor[Each] = SOne                         // each's factor is exactly 1.0
    no u: s.factor.Scalar | s.factor[u] = SZero   // factors are non-zero (strict positivity is the domain)
  }
}

/** units — the configured units of a scheme (the domain of `factor`). */
fun UomScheme.units: set Unit { this.factor.Scalar }

/** toEach — collapse a SINGLE-unit amount to its `each` total: `amt` of unit `u` ⇒ `amt · factor[u]`
    (none if `u` is not configured). The base case of the multi-unit `collapse` (`uom_collapse.als`), which
    folds these products across all of a quantity's units via the keyed Σ. */
fun toEach[sch: UomScheme, u: Unit, amt: Scalar]: lone Scalar {
  some sch.factor[u] => amt.smul[sch.factor[u]] else none
}
