module resources/inventory_item/metrics

/*
 * INVENTORY-COUNT METRICS (DT-007 / PDEV-680) — the READ SIDE: tenant-scoped aggregation of
 * inventory quantities over the InventoryItem universe, as defined in the workbook
 * design-topics/inventory-count-metrics.md. Metrics live NEXT TO the entities they measure (the
 * inventory_item module — Miguel, 2026-07-02; the operations domain is for actual manufacturing/
 * logistics operations like assembly or put-away). This file adds NO facts to the entity or the
 * log — everything is derived (funs/preds) plus the report reification (CountCell + its Σ
 * contribution lines) and the DT-008 bridge.
 *
 * The three moving parts:
 *  1. AS-OF PROJECTIONS — the effective-time (τ: Instant) twins of the log's tick projections:
 *     `IIOcc in Timed` (the P2 opt-in) stamps every occurrence; `stateAsOf`/`liveAsOf` are LOCF
 *     of records over {committed occurrences with at ≤ τ}. Meaningful under `clocksAligned`.
 *  2. FAMILY A — `CountCell` reifies one report cell: (tenant, Item, τ [, locator node@level]).
 *     Members = the LIVE-as-of, tenant-scoped instances classified by the Item (EMPTY included —
 *     zero contribution; retired excluded). The {total, degraded, usable} triple: two
 *     `keyed_sum` folds over per-cell contribution lines (the keyed Σ — same-unit adds, different
 *     units widen, NO conversion: totals are MultiQuantity maps, DT-009/O1), usable derived by
 *     linearity. Locator classification per the literal level-prefix (A1 strict = LBin; A0 = no
 *     level; sub-hierarchy = coarser levels); members with NO locator match only unclassified cells.
 *  3. FAMILY B = A SAMPLED AT PERIOD CLOSES — no new machinery: evaluate a cell at
 *     `endOfPeriod[cal, τ]` (shared/time/calendar's CalendarSpec under `calendarAxioms`). A quiet
 *     period repeats the prior level (LOCF) — a theorem, not a convention.
 *  4. THE DT-008 BRIDGE — `IILevelSignal` re-points the measurement framework at the log: each
 *     committed occurrence touching the watched item EMITS one Measurement stamped with the
 *     occurrence's effective time, valued at the POST-state actual (state records make the level
 *     materialized — no delta fold). THE THEOREM: the framework's LOCF read (`valueAt`) equals the
 *     log's `stateAsOf` — DT-007's "as-of τ" IS the framework's last-measurement-≤-τ metric.
 *
 * Premises (assume per command): `clocksAligned` (forward chronology), `strictChronology` (below,
 * for lone framework reads), `calendarAxioms` (family B only). group/order premises are FACTS via
 * the P2 profile.
 */

open meta/profiles/timed_log                          // PROFILE (DT-012): P2 — the log + wall-clock (Timed, Instant axis)
open resources/inventory_item/inventory_item_implementation  // the log: IIOcc, committed, touches, postFor, retiringFor (intra-module)
open shared/time/calendar                             // CalendarSpec + endOfPeriod/samePeriod (family B closes)
open shared/measurement/quantity                      // Signal/Measurement[Quantity], valueAt (LOCF); keyed_sum[Measurement]
open meta/keyed_value_algebra/keyed_sum[TLine] as ts  // Σ actualQuantity over a cell's members
open meta/keyed_value_algebra/keyed_sum[DLine] as ds  // Σ degradedQty over a cell's members

// ── the P2 opt-in: every InventoryItem occurrence carries its effective-time stamp ──────────────
fact IIOccTimed { IIOcc in Timed }

/** strictChronology — PREMISE: distinct committed occurrences on the SAME item carry distinct
    stamps (strict per-item chronology; `clocksAligned` alone is non-strict). Needed wherever a
    lone by-instant read must pick a unique latest sample (the DT-008 bridge). */
pred strictChronology {
  all disj a, b: IIOcc |
    (committed[a] and committed[b] and some (touches[a] & touches[b])) implies a.at != b.at
}

// ── 1. as-of projections (the τ-twins of occurrences.als' tick projections) ─────────────────────
/** lastTouchAsOf — the latest (by tick) committed occurrence touching `ii` with stamp ≤ τ. */
fun lastTouchAsOf[ii: InventoryItem, t: Instant]: lone IIOcc {
  { o: IIOcc | committed[o] and ii in touches[o] and atOrBefore[o.at, t]
      and (no b: IIOcc | committed[b] and ii in touches[b] and atOrBefore[b.at, t]
             and precedes[o.tick, b.tick]) }
}
/** stateAsOf — LOCF of records over effective time: ii's payload as of τ (tombstone once retired). */
fun stateAsOf[ii: InventoryItem, t: Instant]: lone InventoryItemState {
  postFor[lastTouchAsOf[ii, t], ii]
}
/** liveAsOf — the existence projection over effective time. */
pred liveAsOf[ii: InventoryItem, t: Instant] {
  let o = lastTouchAsOf[ii, t] | some o and not retiringFor[o, ii]
}

// ── 2. locator sub-hierarchy classification (literal level-prefix — O4's convention) ────────────
/** LocLevel — classification depth in the nine-level locator hierarchy (LRegion coarsest … LBin
    finest). Strict locator equality (A1) = LBin; the grand total (A0) = no level at all. */
enum LocLevel { LRegion, LFacility, LArea, LAisle, LBay, LShelf, LTier, LSlot, LBin }

/** samePrefix — p and q agree on every level from region down to `k` (the literal level-prefix
    tuple of the definitions; missing labels compare as "unspecified", forming their own node). */
pred samePrefix[p, q: PhysicalLocator, k: LocLevel] {
  p.region = q.region
  k in LFacility + LArea + LAisle + LBay + LShelf + LTier + LSlot + LBin implies p.facility = q.facility
  k in LArea + LAisle + LBay + LShelf + LTier + LSlot + LBin implies p.area = q.area
  k in LAisle + LBay + LShelf + LTier + LSlot + LBin implies p.aisle = q.aisle
  k in LBay + LShelf + LTier + LSlot + LBin implies p.bay = q.bay
  k in LShelf + LTier + LSlot + LBin implies p.shelf = q.shelf
  k in LTier + LSlot + LBin implies p.tier = q.tier
  k in LSlot + LBin implies p.slot = q.slot
  k = LBin implies p.bin = q.bin
}

// ── 2. family A: the report cell and its members ───────────────────────────────────────────────
/** CountCell — one report cell: the Item's on-hand within a tenant as-of τ, optionally restricted
    to the locator node `cNode` at classification level `cLevel` (both or neither). */
sig CountCell {
  cTenant: one  EntityId,
  cItem:   one  Item,
  cAsOf:   one  Instant,
  cLevel:  lone LocLevel,
  cNode:   lone PhysicalLocator
}
fact CellWellFormed { all c: CountCell | some c.cLevel iff some c.cNode }

/** membersOf — the cell's population: LIVE as-of τ (EMPTY included, retired excluded), in the
    tenant, classified by the Item (in-tenant soft-ref resolution — O6: non-resolving contributes
    nothing), and under the locator node when the cell is classified. */
fun membersOf[c: CountCell]: set InventoryItem {
  { ii: InventoryItem | liveAsOf[ii, c.cAsOf] and ii.tenantId = c.cTenant
      and resolve[ii.itemRef] = c.cItem
      and (some c.cLevel implies
             (some stateAsOf[ii, c.cAsOf].sLocator
              and samePrefix[stateAsOf[ii, c.cAsOf].sLocator, c.cNode, c.cLevel])) }
}

// ── 2. the Σ: one contribution line per (cell, member), folded by keyed_sum ────────────────────
// TWO node types because a keyed_sum instantiation carries ONE `val` per node, and the triple
// needs two independent folds (Σ actual, Σ degraded); usable is derived by linearity, not folded.
/** TLine — a member's actualQuantity contribution to its cell's total. */
sig TLine { tCell: one CountCell, tMember: one InventoryItem }
/** DLine — a member's degradedQty contribution to its cell's degraded total. */
sig DLine { dCell: one CountCell, dMember: one InventoryItem }

// The lines cover each cell's members exactly (one line per member, none for non-members).
fact CellLinesExact {
  all c: CountCell, m: membersOf[c] {
    one l: TLine | l.tCell = c and l.tMember = m
    one l: DLine | l.dCell = c and l.dMember = m
  }
  all l: TLine | l.tMember in membersOf[l.tCell]
  all l: DLine | l.dMember in membersOf[l.dCell]
}

// Pin the two folds (the uom_collapse idiom): node value = the member's as-of quantity map
// (an EMPTY item's map is empty — a zero contribution; absent degraded likewise); chains link
// only within a cell, and each cell's lines form one connected chain (order irrelevant — the
// keyed add is commutative/associative under the profile's group premise).
fact TFold {
  all l: TLine | ts/Fold.val[l] = stateAsOf[l.tMember, l.tCell.cAsOf].sActual.byUnit
  all l: TLine | some ts/Fold.earlier[l] implies ts/Fold.earlier[l].tCell = l.tCell
  all c: CountCell | let g = { l: TLine | l.tCell = c } |
    all disj a, b: g | a in b.^(ts/Fold.earlier) or b in a.^(ts/Fold.earlier)
}
fact DFold {
  all l: DLine | ds/Fold.val[l] = stateAsOf[l.dMember, l.dCell.cAsOf].sDegraded.byUnit
  all l: DLine | some ds/Fold.earlier[l] implies ds/Fold.earlier[l].dCell = l.dCell
  all c: CountCell | let g = { l: DLine | l.dCell = c } |
    all disj a, b: g | a in b.^(ds/Fold.earlier) or b in a.^(ds/Fold.earlier)
}

/** cellTotal — Σ actualQuantity over the cell's members (the keyed map; `zero` for no members). */
fun cellTotal[c: CountCell]: univ -> lone Scalar {
  let g = { l: TLine | l.tCell = c } |
    no g => zero else ts/Fold.cum[{ l: g | no (ts/Fold.earlier).l }]
}
/** cellDegraded — Σ degradedQty over the cell's members. */
fun cellDegraded[c: CountCell]: univ -> lone Scalar {
  let g = { l: DLine | l.dCell = c } |
    no g => zero else ds/Fold.cum[{ l: g | no (ds/Fold.earlier).l }]
}
/** cellUsable — the derived third of the triple: total − degraded (linearity of the keyed Σ). */
fun cellUsable[c: CountCell]: univ -> lone Scalar { add[cellTotal[c], negate[cellDegraded[c]]] }

// ── 4. the DT-008 bridge: the log IS the measurement series ────────────────────────────────────
/** IILevelSignal — the per-InventoryItem on-hand LEVEL signal (piecewise-constant; jumps only at
    committed occurrences). Its measurement history is derived from the log, below. */
sig IILevelSignal extends Signal { watches: one InventoryItem }
fact IILevelIsLevel { all s: IILevelSignal | s.kind = LEVEL }

/** IIMeasurement — a log-emitted sample: which occurrence produced it. */
sig IIMeasurement in Measurement { emittedBy: one IIOcc }

// Event-driven measurement (the DT-007 framework section): each committed occurrence touching the
// watched item emits EXACTLY ONE sample — stamped with the occurrence's effective time, valued at
// the POST-state actual (records materialize the level; no delta fold) — and level signals carry
// no other samples.
fact IILevelWiring {
  all m: Measurement | m.of in IILevelSignal implies
    (m in IIMeasurement and committed[m.emittedBy]
     and m.of.watches in touches[m.emittedBy]
     and m.at = m.emittedBy.at
     and m.value = postFor[m.emittedBy, m.of.watches].sActual)
  all s: IILevelSignal, o: IIOcc | (committed[o] and s.watches in touches[o]) implies
    (one m: Measurement | m.of = s and m.emittedBy = o)
}
