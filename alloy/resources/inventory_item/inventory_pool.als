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
 * CUSTODY (DT-020 §8.5, landed 2026-08-06 — build cut 2A): the I4 pool-side Hold/Release
 * marker — one custody episode per pool (§8.5.1: born-or-attached held ONCE, never re-held),
 * `custody` on the record (held-by-at-most-one is structural: `lone`), the opaque HolderHandle
 * (reconciliation-only). PENDING (cut 2B, lands WITH the holder retrofits — kanban cycle attach,
 * demand holding-attach — because gating adds breaks ungated holders): the §8.5.1(5)
 * PoolAdd-requires-HELD guard clause. PoolRemove stays custody-EXEMPT permanently (§8.5.2:
 * removals are membership-truth corrections; the retirement listener's probe reaches released
 * pools).
 *
 * Inventory counts remain DERIVED, never stored — the counting machinery is the metrics package
 * (`resources/inventory_item/metrics.als`, DT-007); a pool-scoped count cell lands there on
 * demand. The §8.5.2 retirement listener (PoolRemove reaction + probe) lands with the DT-020
 * build's receiving cut.
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
  itemRef: one EntityId             // → Item; constrains membership (immutable)
}

/** Outgoing soft references: the classifier only. (Membership is record-carried, not a soft ref.) */
fact InventoryPoolRefs { all p: InventoryPool | p.dataRefs = p.itemRef }

/** The pool's Item resolves to an actual Item (soft ref — dangling / cross-Universe allowed). */
fact PoolItemIntegrity { all p: InventoryPool | let i = resolve[p.itemRef] | some i implies i in Item }

// ── the state record ─────────────────────────────────────────────────────────────────────────────
/** HolderHandle — the OPAQUE holder identity a Hold carries (§8.5(a); I4's deferred holder id
    un-deferred under the §8.1.3 `sourceHandle` precedent): reconciliation-only — no law reads
    its IDENTITY, laws read custody PRESENCE; a stale hold (missed Release) surfaces as the next
    holder's `RPoolHeld` refusal and is resolved by a handle-guided manual Release (RECONCILED).
    Atoms are nominal. */
sig HolderHandle {}
fact NoOrphanHolderHandle { all h: HolderHandle | h in PoolState.custody + PoolHoldOcc.holder }

/** PoolState — one moment's membership + custody of a pool (a value; extensional).
    `custody` present ⟺ HELD; held-by-at-most-one (I4) is STRUCTURAL (`lone`). */
sig PoolState extends Snapshot { holds: set InventoryItem, custody: lone HolderHandle }
fact PoolStateExtensional {
  all disj a, b: PoolState | a.holds != b.holds or a.custody != b.custody
}

// ── the kinds ────────────────────────────────────────────────────────────────────────────────────
/** PoolOcc — a pool-membership operation occurrence on the spine; `subject` is the pool (pre/post
    are its PoolState records — the spine's SubjectOccRecords). */
abstract sig PoolOcc extends plog/SubjectOcc {}
/** pool — the reading alias for the spine's `subject` field (receiver syntax: `o.pool`). */
fun pool[o: PoolOcc]: one InventoryPool { o.subject }

sig PoolAddOcc    extends PoolOcc { item: one InventoryItem } { bindings = subject + item }
sig PoolRemoveOcc extends PoolOcc { item: one InventoryItem } { bindings = subject + item }

/** Hold — take custody (§8.5): the call-first peer leg every holder drives before its own
    attach commit (cycle attach, demand holding-attach; the receiving line's pool is BORN held).
    ONE custody episode per pool (§8.5.1): `RPoolHeld` refuses both arms — a hold on a held
    pool AND a re-hold after Release (fresh-per-episode; a pool's custody is consumed once). */
sig PoolHoldOcc    extends PoolOcc { holder: one HolderHandle } { bindings = subject + holder }
/** Release — end custody (§8.5(a)): the EXPLICIT closing leg of every holder-closing act (the
    `rolloverFlushReleasesPool` free implicit release traded away); the released pool persists,
    user-manipulable, never re-held. */
sig PoolReleaseOcc extends PoolOcc {} { bindings = subject }

// ── refusal reasons ──────────────────────────────────────────────────────────────────────────────
one sig RWrongItem, RWrongTenant, RAlreadyMember, RNotMember extends Reason {}
/** RPoolHeld — custody unavailable: held now, or the one lifetime episode already consumed
    (§8.5/§8.5.1 — one guard serves both arms because either implies a prior committed Hold).
    RPoolNotHeld — the act needs a held pool (Release without custody; PoolAdd gains this
    clause at cut 2B). */
one sig RPoolHeld, RPoolNotHeld extends Reason {}

// ── the spine adoption: chaining (unconditional — a refused occurrence still read the real
// membership) + v1 result policy ────────────────────────────────────────────────────────────────
fact PoolChaining      { plog/chained }
// (no o.pre = the pool has no committed history: membership reads empty — `none.holds = none`.)

// ── reason-precise admission guards (Accepted ⟺ ∅; because = EXACTLY the set) ────────────────────
fun poolAddViol[o: PoolAddOcc]: set Reason {
  ((o.item.itemRef != o.pool.itemRef)     => RWrongItem     else none)
  + ((o.item.tenantId != o.pool.tenantId) => RWrongTenant   else none)
  + ((o.item in o.pre.holds)              => RAlreadyMember else none)
}
fun poolRemoveViol[o: PoolRemoveOcc]: set Reason {
  // §8.5.2: custody-EXEMPT — removals are membership-truth corrections, legal on held AND
  // released pools (the retirement listener's probe reaches released pools).
  ((o.item not in o.pre.holds) => RNotMember else none)
}
/** priorHold — a committed Hold on `o`'s pool strictly before `o`: the one-custody-episode
    read (§8.5.1). Currently-held and episode-consumed BOTH imply one exists — a log read,
    deliberately not a record read (Release clears `custody`, but never the history). */
fun priorHold[o: PoolOcc]: set PoolHoldOcc {
  { h: PoolHoldOcc | committed[h] and h.subject = o.subject and precedes[h.tick, o.tick] }
}
fun poolHoldViol[o: PoolHoldOcc]: set Reason {
  ((some priorHold[o]) => RPoolHeld else none)
}
fun poolReleaseViol[o: PoolReleaseOcc]: set Reason {
  ((no o.pre.custody) => RPoolNotHeld else none)
}
fact PoolAdmissionWitness {
  all o: PoolAddOcc     | (o.admission = Accepted iff no poolAddViol[o])     and (o.admission in Rejected implies o.admission.because = poolAddViol[o])
  all o: PoolRemoveOcc  | (o.admission = Accepted iff no poolRemoveViol[o])  and (o.admission in Rejected implies o.admission.because = poolRemoveViol[o])
  all o: PoolHoldOcc    | (o.admission = Accepted iff no poolHoldViol[o])    and (o.admission in Rejected implies o.admission.because = poolHoldViol[o])
  all o: PoolReleaseOcc | (o.admission = Accepted iff no poolReleaseViol[o]) and (o.admission in Rejected implies o.admission.because = poolReleaseViol[o])
}
// No result policy in v1 (mirrors the InventoryItem log).
fact PoolCommitAccepts { plog/commitAlwaysAccepts }

// ── effects (membership kinds FRAME custody; custody kinds FRAME membership) ────────────────────
fact PoolEffectWitness {
  all o: PoolAddOcc     | committed[o] implies (o.post.holds = o.pre.holds + o.item and o.post.custody = o.pre.custody)
  all o: PoolRemoveOcc  | committed[o] implies (o.post.holds = o.pre.holds - o.item and o.post.custody = o.pre.custody)
  all o: PoolHoldOcc    | committed[o] implies (o.post.custody = o.holder and o.post.holds = o.pre.holds)
  all o: PoolReleaseOcc | committed[o] implies (no o.post.custody and o.post.holds = o.pre.holds)
}

// ── the projections (wrappers over the spine's reads — public surface preserved) ────────────────
/** lastPoolTouch — the latest committed occurrence on `p` at-or-before `t`. */
fun lastPoolTouch[p: InventoryPool, t: Tick]: lone PoolOcc { plog/lastTouch[p, t] }
/** heldAt — the pool's membership as of `t` (empty before any committed history). */
fun heldAt[p: InventoryPool, t: Tick]: set InventoryItem { plog/recordAt[p, t].holds }
/** custodyAt — the pool's custody as of `t` (§8.5): present ⟺ HELD; the handle is opaque
    (reconciliation-only — compare presence, never identity, in laws). */
fun custodyAt[p: InventoryPool, t: Tick]: lone HolderHandle { plog/recordAt[p, t].custody }
