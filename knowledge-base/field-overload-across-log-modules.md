# Field-name overloading across log-carried modules (the `sStatus` collision)

**Symptom (DT-023 cut 7b, the first two-log-module cone):** "This name is ambiguous due to
multiple matches" at sites that compiled fine for months — e.g.
`o.pre.sStatus = RD_RETIRED` in `item_implementation.als` broke the moment
`business_affiliate` became log-carried.

**Mechanism:** Alloy resolves an overloaded field join by RELEVANCE — candidates whose
range type cannot participate in the enclosing expression are dropped. `ItemState.sStatus`
(range `RdStatus`) coexisted happily with `OrderState.sStatus` (range `OrderStatus`)
because a comparison against `RD_LIVE` kept exactly one candidate. When a SECOND
`RdStatus`-ranged `sStatus` (`BusinessAffiliateState`) entered the cone, generic
`Snapshot`-typed joins (`o.pre.sStatus`, `p.post.sStatus`) had two relevant candidates →
type error.

**Fix pattern:** type-restrict the join at the site — `(o.pre & ItemState).sStatus`,
`(p.post & BusinessAffiliateState).sStatus` — at every lifecycle read/effect site in BOTH
module pairs (types pinnable-pred, contracts shape-pred, implementation viol/effects).
Typed accessors (`oPre`/`rlPre`-style `fun`s) are the heavier alternative when a module has
many such sites.

**Corollary for new reference-data modules (7c's staff/processing_network and beyond):**
any module mirroring the lifecycle pattern re-uses the field NAME `sStatus` with range
`RdStatus` — every one of its generic pre/post joins must be born type-restricted, and
adding such a module can break OTHER modules' un-restricted joins anywhere their cones
meet. Grep for `\.pre\.sStatus|\.post\.sStatus` before landing a new lifecycle module.

Also in this class: a union-typed quantifier over sigs with same-named fields
(`all o: CreateOrderOcc + UpdateSupplierOcc | o.supplier…`) cannot resolve the field even
when both are type-identical — split the quantifier per sig.
