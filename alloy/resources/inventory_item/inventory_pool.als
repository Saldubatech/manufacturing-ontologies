module resources/inventory_item/inventory_pool

/*
 * InventoryPool — a Scoped aggregate of InventoryItems that all classify under ONE Item. It resolves the
 * tension between (a) an InventoryItem as a *homogeneous* amount of goods and (b) needing to discriminate
 * InventoryItems that share an Item but differ in attributes (lot, expiry, locator, …): a consumer
 * references a single `one`/`lone` pool, while the pool holds the discriminating *set* internally — so the
 * `one`-vs-`set` duality is NOT forced on the consuming modules.
 *
 * LOG-CARRIED (2026-07-02 — MP review; the v1 `var items` predated DT-011's one-carrier decision):
 * membership is now the occurrence-log pattern of the rest of this module — the entity is identity
 * only; the held set lives on `PoolState` records carried by `PoolAddOcc`/`PoolRemoveOcc`; the
 * current view is the LOCF projection `heldAt`. Homogeneity and same-tenant are now GUARD-derived
 * theorems (witnessed refusals: `RWrongItem`/`RWrongTenant`), not standing `always` facts. Pool
 * occurrences share the one causal Tick order with the InventoryItem occurrences.
 *
 * Still v1 scope: membership only — no liveness coupling to members (a retired member is a
 * modeling question deferred with reservations). Inventory counts remain DERIVED, never stored —
 * the counting machinery is the metrics package (`resources/inventory_item/metrics.als`, DT-007);
 * a pool-scoped count cell lands there on demand. Consumers (KanbanCard, …) are NOT retrofitted.
 *
 * Future (not modeled): recursive pools (pool-of-pools or leaf items); default/back-fill attributes;
 * lock/unlock the set as a unit; reservations against the set.
 */

open meta/profiles/domain_log                    // PROFILE (DT-012): the log anatomy (StatefulAction, Tick, verdicts)
open meta/kernel                                 // Scoped, Entity, EntityId, resolve
open reference_data/item/item_types            // Item — the membership classifier (TYPES; laws via root mock/impl)
open resources/inventory_item/inventory_item_types     // InventoryItem (+ transitively keyed algebra, values)

/** InventoryPool — the IDENTITY of a tenant-scoped set of InventoryItems under one Item; its
    membership lives on PoolState records in the occurrence log. */
sig InventoryPool extends Scoped {
  itemRef: one EntityId             // → Item; constrains membership (immutable)
}

/** Outgoing soft references: the classifier only. (Membership is record-carried, not a soft ref.) */
fact InventoryPoolRefs { all p: InventoryPool | p.dataRefs = p.itemRef }

/** The pool's Item resolves to an actual Item (soft ref — dangling / cross-Universe allowed). */
fact PoolItemIntegrity { all p: InventoryPool | let i = resolve[p.itemRef] | some i implies i in Item }

// ── the state record ─────────────────────────────────────────────────────────────────────────────
/** PoolState — one moment's membership of a pool (a value; extensional). */
sig PoolState extends Snapshot { holds: set InventoryItem }
fact PoolStateExtensional { all disj a, b: PoolState | a.holds != b.holds }

// ── the kinds ────────────────────────────────────────────────────────────────────────────────────
/** PoolOcc — a pool-membership operation occurrence; `pool` is the subject (pre/post are its
    PoolState records). */
abstract sig PoolOcc extends StatefulAction { pool: one InventoryPool }
fact PoolOccRecords { all o: PoolOcc | (o.pre + o.post) in PoolState }

sig PoolAddOcc    extends PoolOcc { item: one InventoryItem } { bindings = pool + item }
sig PoolRemoveOcc extends PoolOcc { item: one InventoryItem } { bindings = pool + item }

// ── refusal reasons ──────────────────────────────────────────────────────────────────────────────
one sig RWrongItem, RWrongTenant, RAlreadyMember, RNotMember extends Reason {}

// ── chaining (unconditional — a refused occurrence still read the real membership) ───────────────
/** priorPoolOcc — the latest committed pool occurrence on the same pool before `o`. */
fun priorPoolOcc[o: PoolOcc]: lone PoolOcc {
  { b: PoolOcc | committed[b] and b.pool = o.pool and precedes[b.tick, o.tick]
      and (no c: PoolOcc | committed[c] and c.pool = o.pool
             and precedes[b.tick, c.tick] and precedes[c.tick, o.tick]) }
}
fact PoolChaining {
  all o: PoolOcc | let pr = priorPoolOcc[o] | (some pr => o.pre = pr.post else no o.pre)
}
// (no o.pre = the pool has no committed history: membership reads empty — `none.holds = none`.)

// ── reason-precise admission guards (Accepted ⟺ ∅; because = EXACTLY the set) ────────────────────
fun poolAddViol[o: PoolAddOcc]: set Reason {
  ((o.item.itemRef != o.pool.itemRef)     => RWrongItem     else none)
  + ((o.item.tenantId != o.pool.tenantId) => RWrongTenant   else none)
  + ((o.item in o.pre.holds)              => RAlreadyMember else none)
}
fun poolRemoveViol[o: PoolRemoveOcc]: set Reason {
  ((o.item not in o.pre.holds) => RNotMember else none)
}
fact PoolAdmissionWitness {
  all o: PoolAddOcc    | (o.admission = Accepted iff no poolAddViol[o])    and (o.admission in Rejected implies o.admission.because = poolAddViol[o])
  all o: PoolRemoveOcc | (o.admission = Accepted iff no poolRemoveViol[o]) and (o.admission in Rejected implies o.admission.because = poolRemoveViol[o])
}
// No result policy in v1 (mirrors the InventoryItem log).
fact PoolCommitAccepts { all o: PoolOcc | some o.commit implies o.commit = Accepted }

// ── effects ──────────────────────────────────────────────────────────────────────────────────────
fact PoolEffectWitness {
  all o: PoolAddOcc    | committed[o] implies o.post.holds = o.pre.holds + o.item
  all o: PoolRemoveOcc | committed[o] implies o.post.holds = o.pre.holds - o.item
}

// ── the projections ──────────────────────────────────────────────────────────────────────────────
/** lastPoolTouch — the latest committed occurrence on `p` at-or-before `t`. */
fun lastPoolTouch[p: InventoryPool, t: Tick]: lone PoolOcc {
  { o: PoolOcc | committed[o] and o.pool = p and notAfter[o.tick, t]
      and (no b: PoolOcc | committed[b] and b.pool = p and notAfter[b.tick, t]
             and precedes[o.tick, b.tick]) }
}
/** heldAt — the pool's membership as of `t` (empty before any committed history). */
fun heldAt[p: InventoryPool, t: Tick]: set InventoryItem { lastPoolTouch[p, t].post.holds }
