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
 * SPINE (ported 2026-07-17 — DT-015 R2, the last row of the Q5 refactor review): the membership
 * log now rides `meta/subject_log[InventoryPool, PoolState]` — the spine EXTRACTED from this
 * log's hand-built original (with the II and CardCycle logs). The kind subject field is
 * therefore `subject`; the alias `fun pool` preserves every existing `o.pool` read (receiver
 * syntax), so consumers and suites are unchanged; `heldAt` is a wrapper over the spine's
 * `recordAt`.
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
open meta/subject_log/subject_log[InventoryPool, PoolState] as plog

/** InventoryPool — the IDENTITY of a tenant-scoped set of InventoryItems under one Item; its
    membership lives on PoolState records in the occurrence log. */
sig InventoryPool extends Scoped {
  itemPin: one ItemOcc              // → Item VERSION PIN (DT-023 R3; was itemRef): constrains
                                    //   membership (immutable); entity-wise reads via `.subject`.
                                    //   Genesis is runtime-side (no create kind), so pin CURRENCY
                                    //   anchors at the minting process (receiving) — here only
                                    //   typing + tenancy.
}

// The classifier is a PIN (typed, never dangles) — no soft dataRefs remain on the identity.
fact InventoryPoolRefs { all p: InventoryPool | no p.dataRefs }

// Pin tenancy (DT-023): kernel isolation reaches only EntityId dataRefs — stated here instead.
fact PoolPinTenancy { all p: InventoryPool | p.itemPin.subject.tenantId = p.tenantId }

// ── the state record ─────────────────────────────────────────────────────────────────────────────
/** PoolState — one moment's membership of a pool (a value; extensional). */
sig PoolState extends Snapshot { holds: set InventoryItem }
fact PoolStateExtensional { all disj a, b: PoolState | a.holds != b.holds }

// ── the kinds ────────────────────────────────────────────────────────────────────────────────────
/** PoolOcc — a pool-membership operation occurrence on the spine; `subject` is the pool (pre/post
    are its PoolState records — the spine's SubjectOccRecords). */
abstract sig PoolOcc extends plog/SubjectOcc {}
/** pool — the reading alias for the spine's `subject` field (receiver syntax: `o.pool`). */
fun pool[o: PoolOcc]: one InventoryPool { o.subject }

sig PoolAddOcc    extends PoolOcc { item: one InventoryItem } { bindings = subject + item }
sig PoolRemoveOcc extends PoolOcc { item: one InventoryItem } { bindings = subject + item }

// ── refusal reasons ──────────────────────────────────────────────────────────────────────────────
one sig RWrongItem, RWrongTenant, RAlreadyMember, RNotMember extends Reason {}

// ── the spine adoption: chaining (unconditional — a refused occurrence still read the real
// membership) + v1 result policy ────────────────────────────────────────────────────────────────
fact PoolChaining      { plog/chained }
// (no o.pre = the pool has no committed history: membership reads empty — `none.holds = none`.)

// ── reason-precise admission guards (Accepted ⟺ ∅; because = EXACTLY the set) ────────────────────
fun poolAddViol[o: PoolAddOcc]: set Reason {
  ((o.item.itemPin.subject != o.pool.itemPin.subject) => RWrongItem else none)
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
fact PoolCommitAccepts { plog/commitAlwaysAccepts }

// ── effects ──────────────────────────────────────────────────────────────────────────────────────
fact PoolEffectWitness {
  all o: PoolAddOcc    | committed[o] implies o.post.holds = o.pre.holds + o.item
  all o: PoolRemoveOcc | committed[o] implies o.post.holds = o.pre.holds - o.item
}

// ── the projections (wrappers over the spine's reads — public surface preserved) ────────────────
/** lastPoolTouch — the latest committed occurrence on `p` at-or-before `t`. */
fun lastPoolTouch[p: InventoryPool, t: Tick]: lone PoolOcc { plog/lastTouch[p, t] }
/** heldAt — the pool's membership as of `t` (empty before any committed history). */
fun heldAt[p: InventoryPool, t: Tick]: set InventoryItem { plog/recordAt[p, t].holds }
