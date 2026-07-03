module resources/kanban_card/cycle_state

/*
 * CycleState — the reified STATE RECORD of a CardCycle (DT-015 Phase A): the cycle's mutable
 * payload as a value (a `Snapshot`), carried by the cycle's operation occurrences
 * (cycle_occurrences.als) — the same pattern as InventoryItemState (DT-006 build). Phase A builds
 * this ALONGSIDE the standing structural model: the entity's `status`/`lastEvent`/
 * `executionStatus` fields remain until Phase B slims them away.
 *
 * The record carries ONLY the mutable payload; identity (eId, tenantId, precededBy, the card's
 * containment) stays on the CardCycle entity. `sStatus` ranges over the 8 CORE states —
 * AVAILABLE is a card-level condition (no live cycle), never a cycle state (KC-MH-6); here that
 * is a record FACT, so an AVAILABLE-status record is unrepresentable by construction.
 */

open meta/profiles/domain_log                 // PROFILE (DT-012): the log anatomy
open shared/values                            // Quantity, PhysicalLocator
open resources/kanban_card/card_cycle         // KanbanCardStatus (the 8 core states + AVAILABLE)
open resources/inventory_item/inventory_pool  // InventoryPool — the cycle's BIN (sPool soft-ref target)

/** CycleState — one moment's mutable payload of a CardCycle (a value; extensional). */
sig CycleState extends Snapshot {
  sStatus:          one  KanbanCardStatus,   // operational state (core 8 — fact below)
  sLocator:         lone PhysicalLocator,    // where the card is (VALUE ref). Absent = position not
                                             //   operationally tracked on this leg. NB currently
                                             //   DORMANT: no operation writes it yet — the writer
                                             //   arrives with Receiving/moves (DT-014 rung 4)
  sPool:            lone EntityId,           // → InventoryPool — the cycle's BIN (KD12 revised
                                             //   2026-07-03: pool-mediated materials; absent = no
                                             //   bin attached (the demand leg); attached EMPTY at
                                             //   StartProcessing; pool-present-but-empty ≠ detached)
  sQuantityOverride: lone Quantity           // per-cycle override of the card's nominalQuantity
}

// Value semantics: a state IS its fields.
fact CycleStateExtensional {
  all disj a, b: CycleState |
    a.sStatus != b.sStatus or a.sLocator != b.sLocator
    or a.sPool != b.sPool or a.sQuantityOverride != b.sQuantityOverride
}

// The bin ref is TYPED (soft — dangling/cross-Universe allowed): a resolved sPool is an InventoryPool.
// (Tenancy is occurrence-side — the attach guard — since a record cannot know its cycle's tenant.)
fact CyclePoolIntegrity {
  all s: CycleState | let p = resolve[s.sPool] | some p implies p in InventoryPool
}

// KC-MH-6 as a record fact: a cycle state is always one of the 8 core states.
fact CycleStateIsCore { all s: CycleState | s.sStatus != AVAILABLE }

// ── the canonical REGION ORDER over the core states (KD8) — the forward-skip guard's yardstick ──
/** regionRank — the canonical progression position of each core state (REQUESTING first). */
fun regionRank[st: KanbanCardStatus]: one Int {
  st = REQUESTING => 1 else st = REQUESTED => 2 else st = IN_PROCESS => 3
  else st = READY => 4 else st = FULFILLING => 5 else st = FULFILLED => 6
  else st = IN_USE => 7 else st = DEPLETED => 8 else 0   // AVAILABLE: unranked (unreachable on records)
}
/** regionBefore — `a` strictly precedes `b` on the canonical progression. */
pred regionBefore[a, b: KanbanCardStatus] { regionRank[a] < regionRank[b] }
/** regionBetween — `m` sits strictly between `a` and `b` on the progression. */
pred regionBetween[m, a, b: KanbanCardStatus] { regionBefore[a, m] and regionBefore[m, b] }
