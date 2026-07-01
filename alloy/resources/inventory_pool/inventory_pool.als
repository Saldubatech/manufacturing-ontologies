module resources/inventory_pool/inventory_pool

/*
 * InventoryPool — a Scoped aggregate of InventoryItems that all classify under ONE Item. It resolves the
 * tension between (a) an InventoryItem as a *homogeneous* amount of goods and (b) needing to discriminate
 * InventoryItems that share an Item but differ in attributes (lot, expiry, locator, …): a consumer
 * references a single `one`/`lone` pool, while the pool holds the discriminating *set* internally — so the
 * `one`-vs-`set` duality is NOT forced on the consuming modules.
 *
 * v1 (this checkpoint): membership only. The held set is `var` (add / remove). Inventory counts are
 * DERIVED, not stored (the full total is the cross-sectional keyed Σ of members' quantities — the same
 * pattern as DT-007 / CardCycle.consolidatedActual, deferred; a lightweight `poolIsEmpty` predicate is
 * provided now). Consumers (KanbanCard, …) are deliberately NOT retrofitted here.
 *
 * Future (not modeled): recursive pools (pool-of-pools or leaf items); default/back-fill attributes;
 * lock/unlock the set as a unit; reservations against the set.
 */

open meta/kernel                                 // Scoped, Entity, EntityId, resolve
open reference_data/item/item                    // Item — the membership classifier
open resources/inventory_item/inventory_item     // InventoryItem (+ transitively keyed algebra, values)

/** InventoryPool — a tenant-scoped set of InventoryItems under one Item. */
sig InventoryPool extends Scoped {
  itemRef:   one EntityId,        // → Item; constrains membership (immutable)
  var items: set InventoryItem    // the held InventoryItems (mutable via add / remove)
}

/** Outgoing soft references: the classifier only. (`items` is a direct in-Universe aggregate, not a soft
    reference, so it is not part of `dataRefs`.) */
fact InventoryPoolRefs { all p: InventoryPool | p.dataRefs = p.itemRef }

/** The pool's Item resolves to an actual Item (soft ref — dangling / cross-Universe allowed). */
fact PoolItemIntegrity { all p: InventoryPool | let i = resolve[p.itemRef] | some i implies i in Item }

/** Homogeneity (per-state — `always`, §3.2, since `items` is `var`): every member classifies under the
    pool's Item. */
fact PoolMembershipHomogeneous {
  always all p: InventoryPool | all ii: p.items | ii.itemRef = p.itemRef
}

/** Same tenant (per-state): a pool holds only same-tenant items (both are Scoped). */
fact PoolMembersInTenant {
  always all p: InventoryPool | all ii: p.items | ii.tenantId = p.tenantId
}

/** poolIsEmpty — a lightweight DERIVED reading: the pool holds no on-hand quantity (every member is zero).
    The full inventory count (a keyed Quantity total) is the cross-sectional keyed Σ over `items` — derived,
    not stored; wired when DT-007 lands. */
pred poolIsEmpty[p: InventoryPool] { all ii: p.items | isZero[ii.actualQuantity.byUnit] }

/** addItem — add an InventoryItem (of the pool's Item, same tenant, not already held) to the pool. */
pred addItem[p: InventoryPool, ii: InventoryItem] {
  ii.itemRef = p.itemRef                            // guard: same Item        (else Rejected:WrongItem)
  ii.tenantId = p.tenantId                          // guard: same tenant      (else Rejected:WrongTenant)
  ii not in p.items                                 // guard: not a member yet (else Rejected:AlreadyMember)
  p.items' = p.items + ii                           // effect
  all q: InventoryPool - p | q.items' = q.items     // frame: other pools unchanged
}

/** removeItem — remove a held InventoryItem from the pool. */
pred removeItem[p: InventoryPool, ii: InventoryItem] {
  ii in p.items                                     // guard: is a member      (else Rejected:NotMember)
  p.items' = p.items - ii                           // effect
  all q: InventoryPool - p | q.items' = q.items     // frame: other pools unchanged
}
