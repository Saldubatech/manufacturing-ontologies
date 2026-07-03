module resources/inventory_item/inventory_item_contracts

/*
 * INVENTORY ITEM — CONTRACTS (DT-017). The module's PROMISE to consumers, as named predicates
 * over the TYPES vocabulary only (the reified observables `stateRel`/`liveTicks` and the
 * identity fields) — no occurrence kinds, no guards, no log machinery may appear here.
 *
 * Curated deliberately small (few, strong laws): everything else the implementation proves
 * (conservation across Split/Merge, reason-precise refusals, per-kind frames) is
 * implementation-suite evidence, NOT promised — consumers may not rely on it. Publishing an
 * additional law later is a compatible extension; the reverse is a break.
 *
 * These are THEOREMS of the implementation (discharged in tests/unit/inventory_item.als
 * against the real log) and AXIOMS for consumers (assumed by opening inventory_item_mock.als).
 * The record well-formedness laws (cone, fill-empty, degraded≤actual) are definitional facts
 * in the types file — consumers get them for free; they are not restated here.
 */

open resources/inventory_item/inventory_item_types

// ── L1: the state function ───────────────────────────────────────────────────────────────────────
/** Once an InventoryItem has a state record at some tick, it has EXACTLY ONE at every tick from
    then on (LOCF persistence; `lone` field typing supplies uniqueness). Consumers may treat
    `stateAt` as a total function of (started item, tick) — no gaps, no forks. */
pred stateIsFunctionOnceStarted {
  all ii: InventoryItem, t1, t2: Tick |
    (some ii.stateRel[t1] and notAfter[t1, t2]) implies some ii.stateRel[t2]
}

// ── L2: liveness presupposes history ─────────────────────────────────────────────────────────────
/** An item is live only at ticks where it has a state record: existence is never asserted
    without a payload to read. */
pred liveHaveState {
  all ii: InventoryItem, t: Tick | t in ii.liveTicks implies some ii.stateRel[t]
}

// ── L3: items are born live ──────────────────────────────────────────────────────────────────────
/** At the first tick an item has a state record, it is live — history begins with existence,
    never with a tombstone. */
pred bornLive {
  all ii: InventoryItem, t: Tick |
    (some ii.stateRel[t] and (no t2: Tick | precedes[t2, t] and some ii.stateRel[t2]))
      implies t in ii.liveTicks
}

// ── L4: closure is terminal ──────────────────────────────────────────────────────────────────────
/** Once a started item is not live, it never becomes live again (no resurrection — the
    observable face of the license-plate non-reuse rule). Consumers may treat the live span as
    a single interval. */
pred closureIsTerminal {
  all ii: InventoryItem, t1, t2: Tick |
    (some ii.stateRel[t1] and t1 not in ii.liveTicks and notAfter[t1, t2])
      implies t2 not in ii.liveTicks
}

// ── the promise ──────────────────────────────────────────────────────────────────────────────────
/** guarantees — the module's full promise: the conjunction of the published laws. */
pred guarantees { stateIsFunctionOnceStarted and liveHaveState and bornLive and closureIsTerminal }
