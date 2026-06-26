module resources/inventory_item/operations

open resources/inventory_item/inventory_item

/*
 * InventoryItem operations (v1) as TRANSITION PREDICATES over the effective timeline (Phase B,
 * DT-004 / DT-006). Each predicate relates the current state to the next (`'` = next-state value):
 * guards read the current state, postconditions constrain the next. Identity is preserved for free
 * (the immutable fields — eId, itemRef, licensePlate, serialNumber, minQuantity — are constant
 * across the trace); Create/Delete/WriteOff/Merge move atoms in and out of `Live`.
 *
 * The companion design spec is workbook resources/inventory_item/operations.md (parameters,
 * pre/post, rejection results). The per-state domain invariants (cone, EMPTY⟹no-qualifiers,
 * degraded≤actual) live in inventory_item.als as `always` facts and do enforcement work here:
 * a transition whose next-state would violate them is simply unsatisfiable (that is how the
 * "Rejected:*" guards bite — e.g. an over-consume would drive `actual` out of the cone).
 *
 * Privileged ops (WriteOff, ForceMove) carry no authorization check yet — the actor/permission
 * layer is deferred (DT-006). They are modeled as their own predicates (unfolded from the old
 * force flags) so that layer can attach a guard per operation later; here they differ from their
 * non-privileged siblings only by dropping the state guard (any Fill / overrides LOCKED).
 */

// ── frame helpers — the 7 mutable (var) fields ────────────────────────────────────────
/** sameQty — actual + degraded unchanged next state. */
pred sameQty[ii: InventoryItem]   { ii.actualQuantity' = ii.actualQuantity and ii.degradedQty' = ii.degradedQty }
/** sameLots — lot set unchanged. */
pred sameLots[ii: InventoryItem]  { ii.lotNumbers' = ii.lotNumbers }
/** sameLoc — locator unchanged. */
pred sameLoc[ii: InventoryItem]   { ii.locator' = ii.locator }
/** sameAdmin — administrative state unchanged. */
pred sameAdmin[ii: InventoryItem] { ii.administrativeState' = ii.administrativeState }
/** sameDesc — descriptive notes/colorCode unchanged. */
pred sameDesc[ii: InventoryItem]  { ii.notes' = ii.notes and ii.colorCode' = ii.colorCode }
/** sameExp — expiration unchanged (D17). */
pred sameExp[ii: InventoryItem]   { ii.expirationDate' = ii.expirationDate }
/** minExp — the earlier of two expirations (D17), with ABSENT = "never" = +∞: absent loses to any
    present date; both absent ⇒ absent. (Int timestamp placeholder; native `<` comparison.) */
fun minExp[a, b: lone Int]: lone Int { no a => b else (no b => a else (a < b => a else b)) }
/** sameFill — fill state unchanged (D16: SEALED survives ops that don't change the real quantity). */
pred sameFill[ii: InventoryItem]  { ii.fillState' = ii.fillState }
/** demoteFill — any real-quantity change lands in OPEN, or EMPTY when the new on-hand is zero (D16). */
pred demoteFill[ii: InventoryItem] { ii.fillState' = (isZero[ii.actualQuantity'.byUnit] => EMPTY else OPEN) }
/** sameState — every mutable field unchanged (a fully-framed item). */
pred sameState[ii: InventoryItem] { sameQty[ii] and sameLots[ii] and sameLoc[ii] and sameAdmin[ii] and sameDesc[ii] and sameFill[ii] and sameExp[ii] }
/** othersUnchanged — every OTHER live item is fully framed (the operation touches only `xs`). */
pred othersUnchanged[xs: set InventoryItem] { all jj: Live - xs | sameState[jj] }

// ── the legal-transition relation ────────────────────────────────────────────────────────
/** someOp — SOME operation fires this step (a representative instantiation of each). The legal-
    transition relation; trace-level lifecycle checks condition on it (`always (someOp implies …)`)
    so they constrain only real operation steps, not the arbitrary var changes Alloy otherwise allows. */
pred someOp {
  (some ii: InventoryItem, q: Quantity | create[ii, q, none])
  or (some ii: InventoryItem | delete[ii])
  or (some ii: InventoryItem | writeOff[ii])
  or (some ii: InventoryItem, q: Quantity | replenish[ii, q, none, none])
  or (some ii: InventoryItem, q: Quantity | consume[ii, q])
  or (some ii: InventoryItem, loc: PhysicalLocator | move[ii, loc])
  or (some ii: InventoryItem, loc: PhysicalLocator | forceMove[ii, loc])
  or (some ii: InventoryItem | lock[ii])
  or (some ii: InventoryItem | unlock[ii])
  or (some ii: InventoryItem | seal[ii])
  or (some ii: InventoryItem | unseal[ii])
  or (some ii: InventoryItem, d: Quantity | inspect[ii, d])
  or (some ii: InventoryItem | inspect[ii, none])
  or (some ii: InventoryItem, g: Quantity | adjustQuantity[ii, g, none])
  or (some ii: InventoryItem, t: Text | adjustProperties[ii, t, none])
  or (some ii: InventoryItem, g: Quantity | rePack[ii, g, none])
  or (some o, n: InventoryItem, q: Quantity | split[o, n, q, none])
  or (some s, a: InventoryItem | merge[s, a])
}

// ── lifecycle ─────────────────────────────────────────────────────────────────────────
/** Create — bring a fresh item into existence with a strictly positive initial quantity, UNLOCKED,
    no degraded/lots/locator/descriptors, fill = OPEN (D16 — creation presumes no operator intent;
    `seal` asserts SEALED later). Identity (itemRef, licensePlate, serial, minQuantity) is eternal. */
pred create[ii: InventoryItem, qty: Quantity, expiration: lone Int] {
  ii not in Live and ii not in Retired                            // pre: a genuinely fresh atom (never lived)
  classify[qty.byUnit] = POSITIVE                                 // strictly positive (no empty placeholders)
  // post
  Live' = Live + ii
  Retired' = Retired
  ii.actualQuantity' = qty
  no ii.degradedQty'
  no ii.lotNumbers'
  ii.fillState' = OPEN                                            // D16: born OPEN (no intent presumed)
  ii.administrativeState' = UNLOCKED
  no ii.locator'
  no ii.notes' and no ii.colorCode'
  ii.expirationDate' = expiration                                 // D17: born with the given expiry (none ⇒ never)
  othersUnchanged[ii]
}

/** Delete — remove an EMPTY item; its license plate retires with it (never reused — the immutable
    plate stays bound to this atom forever). */
pred delete[ii: InventoryItem] {
  ii in Live
  ii.fillState = EMPTY                                            // else Rejected:NotApplicable (use WriteOff)
  Live' = Live - ii
  Retired' = Retired + ii                                         // terminal — the atom + its LPN retire forever
  othersUnchanged[ii]
}

/** WriteOff (privileged) — remove a non-empty item (administrative write-off). Authorization
    deferred (DT-006); differs from Delete only by allowing any Fill. */
pred writeOff[ii: InventoryItem] {
  ii in Live
  Live' = Live - ii
  Retired' = Retired + ii
  othersUnchanged[ii]
}

// ── boundary flows ──────────────────────────────────────────────────────────────────────
/** Replenish — add a strictly positive delta from outside; may revive an EMPTY item. UNLOCKED and
    not DISABLED; lots unioned; serialized ⇒ only from Zero. */
pred replenish[ii: InventoryItem, delta: Quantity, lots: set LotNumber, expiration: lone Int] {
  ii in Live
  ii.administrativeState = UNLOCKED                               // else Rejected:Locked
  ii.operationalState != DISABLED                                 // else Rejected:Unfit
  classify[delta.byUnit] = POSITIVE                               // else Rejected:NonPositive
  isSerialized[ii] implies isZero[ii.actualQuantity.byUnit]       // serialized: only from Zero (D10)
  // post
  ii.actualQuantity'.byUnit = add[ii.actualQuantity.byUnit, delta.byUnit]
  ii.lotNumbers' = ii.lotNumbers + lots
  ii.degradedQty' = ii.degradedQty
  ii.fillState' = OPEN                                            // D16: real quantity changed (actual' > 0)
  ii.expirationDate' = minExp[ii.expirationDate, expiration]      // D17: incoming stock can only SHORTEN expiry
  sameLoc[ii] and sameAdmin[ii] and sameDesc[ii]
  Live' = Live
  Retired' = Retired
  othersUnchanged[ii]
}

/** Consume — remove a strictly positive delta ≤ available (no over-consume). UNLOCKED, not DISABLED,
    non-empty; consume-to-zero clears degraded + lots (G3) and auto-yields ENABLED (derived);
    serialized ⇒ only the full available amount. */
pred consume[ii: InventoryItem, amount: Quantity] {
  ii in Live
  ii.administrativeState = UNLOCKED                               // else Rejected:Locked
  ii.operationalState != DISABLED                                 // else Rejected:Unfit
  ii.fillState != EMPTY
  classify[amount.byUnit] = POSITIVE                              // else Rejected:NonPositive
  lte[amount.byUnit, ii.availableQty]                             // else Rejected:Overdraw
  isSerialized[ii] implies semanticEq[amount.byUnit, ii.availableQty] = EQUAL   // serialized: full only (D10)
  // post
  ii.actualQuantity'.byUnit = add[ii.actualQuantity.byUnit, negate[amount.byUnit]]
  (isZero[ii.actualQuantity'.byUnit])
     => (no ii.degradedQty' and no ii.lotNumbers')                // consume-to-zero: husk
     else (ii.degradedQty' = ii.degradedQty and ii.lotNumbers' = ii.lotNumbers)
  demoteFill[ii]                                                  // D16: → EMPTY (to zero) or OPEN
  sameLoc[ii] and sameAdmin[ii] and sameDesc[ii] and sameExp[ii]   // D17: removing stock doesn't change expiry
  Live' = Live
  Retired' = Retired
  othersUnchanged[ii]
}

// ── redistribution (conserve) ───────────────────────────────────────────────────────────
/** Move — relocate the whole item; UNLOCKED; identity-preserving (only the locator changes). */
pred move[ii: InventoryItem, loc: PhysicalLocator] {
  ii in Live
  ii.administrativeState = UNLOCKED                               // else Rejected:Locked (use ForceMove)
  ii.locator' = loc
  sameQty[ii] and sameLots[ii] and sameAdmin[ii] and sameDesc[ii] and sameFill[ii] and sameExp[ii]   // D16: locator change preserves SEALED; D17 expiry
  Live' = Live
  Retired' = Retired
  othersUnchanged[ii]
}

/** ForceMove (privileged) — relocate regardless of LOCKED (administrative override). Authorization
    deferred (DT-006); differs from Move only by dropping the UNLOCKED guard. */
pred forceMove[ii: InventoryItem, loc: PhysicalLocator] {
  ii in Live
  ii.locator' = loc
  sameQty[ii] and sameLots[ii] and sameAdmin[ii] and sameDesc[ii] and sameFill[ii] and sameExp[ii]   // D16: locator change preserves SEALED; D17 expiry
  Live' = Live
  Retired' = Retired
  othersUnchanged[ii]
}

/** Split — divide off a homogeneous sub-bundle (good and/or degraded portion) onto a freshly-minted
    in-place item `nu`; conserves quantity per portion; copies the full lot set; the remainder may be
    an empty husk. Rejected for serialized items (D10). */
pred split[orig, nu: InventoryItem, splitOff: lone Quantity, degSplit: lone Quantity] {
  orig != nu
  orig in Live and nu not in Live and nu not in Retired          // nu is a genuinely fresh atom
  not isSerialized[orig] and not isSerialized[nu]                 // else Rejected:Serialized
  nu.itemRef = orig.itemRef and nu.tenantId = orig.tenantId       // same cell identity (immutable)
  some splitOff or some degSplit                                  // else Rejected:NonPositive
  some splitOff implies classify[splitOff.byUnit] = POSITIVE
  some degSplit implies classify[degSplit.byUnit] = POSITIVE
  some splitOff implies lte[splitOff.byUnit, orig.availableQty]   // else Rejected:Overdraw
  some degSplit implies lte[degSplit.byUnit, orig.degradedQty.byUnit]
  let soGood = (some splitOff => splitOff.byUnit else zero) |
  let soDeg  = (some degSplit => degSplit.byUnit else zero) |
  let soTot  = add[soGood, soDeg] |
  let remDeg = add[orig.degradedQty.byUnit, negate[soDeg]] {
    // new item nu
    nu.actualQuantity'.byUnit = soTot
    (isZero[soDeg]) => no nu.degradedQty' else nu.degradedQty'.byUnit = soDeg
    nu.lotNumbers' = orig.lotNumbers                              // full lot copy (D11)
    nu.fillState' = OPEN                                          // D16: born OPEN (a split-off is a creation)
    nu.administrativeState' = orig.administrativeState
    nu.locator' = orig.locator
    nu.notes' = orig.notes and nu.colorCode' = orig.colorCode
    nu.expirationDate' = orig.expirationDate                      // D17: split-off inherits the same expiry
    // original remainder
    orig.actualQuantity'.byUnit = add[orig.actualQuantity.byUnit, negate[soTot]]
    (isZero[orig.actualQuantity'.byUnit])
      => (no orig.degradedQty' and no orig.lotNumbers')           // husk
      else { (isZero[remDeg]) => no orig.degradedQty' else orig.degradedQty'.byUnit = remDeg
             orig.lotNumbers' = orig.lotNumbers }
    demoteFill[orig]                                              // D16: remainder's real quantity changed
    sameLoc[orig] and sameAdmin[orig] and sameDesc[orig] and sameExp[orig]   // D17: remainder keeps its expiry
  }
  Live' = Live + nu
  Retired' = Retired
  othersUnchanged[orig + nu]
}

/** Merge — absorb `absorbed` into `surv` (identical Item + locator); sum quantities + degraded,
    union lots; `absorbed` retires. Rejected for serialized items (D10). */
pred merge[surv, absorbed: InventoryItem] {
  surv != absorbed
  surv in Live and absorbed in Live
  not isSerialized[surv] and not isSerialized[absorbed]           // else Rejected:Serialized
  surv.tenantId = absorbed.tenantId and surv.itemRef = absorbed.itemRef and surv.locator = absorbed.locator  // identical cell
  // post: survivor sums
  surv.actualQuantity'.byUnit = add[surv.actualQuantity.byUnit, absorbed.actualQuantity.byUnit]
  let dsum = add[surv.degradedQty.byUnit, absorbed.degradedQty.byUnit] |
    (isZero[dsum]) => no surv.degradedQty' else surv.degradedQty'.byUnit = dsum
  surv.lotNumbers' = surv.lotNumbers + absorbed.lotNumbers
  surv.expirationDate' = minExp[surv.expirationDate, absorbed.expirationDate]   // D17: earliest of the two
  demoteFill[surv]                                                // D16: survivor's real quantity changed (→ OPEN)
  sameLoc[surv] and sameAdmin[surv] and sameDesc[surv]
  Live' = Live - absorbed
  Retired' = Retired + absorbed
  othersUnchanged[surv + absorbed]
}

// ── re-expression / correction / property ─────────────────────────────────────────────────
/** rePack — re-express the good and/or degraded portion in a new UoM basis (caller-asserted, no
    correctness claim). Non-serialized, non-empty, emptiness-preserving (post non-empty); degraded ≤
    actual; lots unchanged. PRESERVES Fill (D16): re-expressing units is NOT a change in the real
    quantity, so a SEALED item rePacked stays SEALED. */
pred rePack[ii: InventoryItem, newGood: lone Quantity, newDeg: lone Quantity] {
  ii in Live
  not isSerialized[ii]                                            // else Rejected:Serialized
  ii.fillState != EMPTY                                           // else Rejected:Empty
  some newGood or some newDeg
  some newGood implies classify[newGood.byUnit] in (ZERO + POSITIVE)
  some newDeg  implies classify[newDeg.byUnit]  in (ZERO + POSITIVE)
  let dmap = (some newDeg  => newDeg.byUnit  else ii.degradedQty.byUnit) |
  let gmap = (some newGood => newGood.byUnit else ii.availableQty) |
  let amap = add[gmap, dmap] {
    lte[dmap, amap]                                               // degraded ≤ actual (else Rejected:Incompatible)
    not isZero[amap]                                              // emptiness-preserving (non-zero stays non-zero)
    ii.actualQuantity'.byUnit = amap
    (isZero[dmap]) => no ii.degradedQty' else ii.degradedQty'.byUnit = dmap
  }
  ii.lotNumbers' = ii.lotNumbers
  sameFill[ii]                                                    // D16: re-expression preserves SEALED
  sameLoc[ii] and sameAdmin[ii] and sameDesc[ii] and sameExp[ii]   // D17: re-expression preserves expiry
  Live' = Live
  Retired' = Retired
  othersUnchanged[ii]
}

/** AdjustQuantity — set quantity to an observed count (the only non-conservative quantity op);
    observedGood ≥ 0 (may be zero), optional observedDegraded; permitted in any Admin/Op state
    (incl. LOCKED). actual' = observedGood + degraded'; to-zero clears qualifiers (G3). */
pred adjustQuantity[ii: InventoryItem, observedGood: Quantity, observedDeg: lone Quantity] {
  ii in Live
  classify[observedGood.byUnit] in (ZERO + POSITIVE)
  some observedDeg implies classify[observedDeg.byUnit] in (ZERO + POSITIVE)
  let dmap = (some observedDeg => observedDeg.byUnit else ii.degradedQty.byUnit) |
  let amap = add[observedGood.byUnit, dmap] {
    ii.actualQuantity'.byUnit = amap
    (isZero[amap])
      => (no ii.degradedQty' and no ii.lotNumbers')               // reconciled to empty
      else { (isZero[dmap]) => no ii.degradedQty' else ii.degradedQty'.byUnit = dmap
             ii.lotNumbers' = ii.lotNumbers }
  }
  demoteFill[ii]                                                  // D16: a count is a real-quantity write
  sameLoc[ii] and sameAdmin[ii] and sameDesc[ii] and sameExp[ii]   // D17: a count doesn't change expiry
  Live' = Live
  Retired' = Retired
  othersUnchanged[ii]
}

/** AdjustProperties — atomically correct the v1 descriptive keys (notes, colorCode); ≥ 1 update;
    no quantity / state / identity change. */
pred adjustProperties[ii: InventoryItem, newNotes: lone Text, newColor: lone Text] {
  ii in Live
  some newNotes or some newColor                                 // non-empty updates (else Rejected:NotApplicable)
  (some newNotes => ii.notes'     = newNotes else ii.notes'     = ii.notes)
  (some newColor => ii.colorCode' = newColor else ii.colorCode' = ii.colorCode)
  sameQty[ii] and sameLots[ii] and sameLoc[ii] and sameAdmin[ii] and sameFill[ii] and sameExp[ii]
  Live' = Live
  Retired' = Retired
  othersUnchanged[ii]
}

// ── assessment / administrative ───────────────────────────────────────────────────────────
/** Inspect — set the worthiness driver `degradedQty` (absent/zero ⇒ clears to ENABLED). Non-empty;
    degraded ≤ actual; serialized ⇒ 0 or full. Only Operational (derived) changes. */
pred inspect[ii: InventoryItem, deg: lone Quantity] {
  ii in Live
  ii.fillState != EMPTY                                          // else Rejected:Empty
  some deg implies (classify[deg.byUnit] in (ZERO + POSITIVE) and lte[deg.byUnit, ii.actualQuantity.byUnit])
  isSerialized[ii] implies (no deg or isZero[deg.byUnit] or semanticEq[deg.byUnit, ii.actualQuantity.byUnit] = EQUAL)
  // post
  ii.actualQuantity' = ii.actualQuantity
  (no deg or isZero[deg.byUnit]) => no ii.degradedQty' else ii.degradedQty' = deg
  sameLots[ii] and sameLoc[ii] and sameAdmin[ii] and sameDesc[ii] and sameFill[ii] and sameExp[ii]   // D16: inspection preserves SEALED; D17 expiry
  Live' = Live
  Retired' = Retired
  othersUnchanged[ii]
}

/** Lock — administrative hold (UNLOCKED → LOCKED). */
pred lock[ii: InventoryItem] {
  ii in Live
  ii.administrativeState = UNLOCKED                              // else Rejected:NotApplicable
  ii.administrativeState' = LOCKED
  sameQty[ii] and sameLots[ii] and sameLoc[ii] and sameDesc[ii] and sameFill[ii] and sameExp[ii]
  Live' = Live
  Retired' = Retired
  othersUnchanged[ii]
}

/** Unlock — release the hold (LOCKED → UNLOCKED). */
pred unlock[ii: InventoryItem] {
  ii in Live
  ii.administrativeState = LOCKED                                // else Rejected:NotApplicable
  ii.administrativeState' = UNLOCKED
  sameQty[ii] and sameLots[ii] and sameLoc[ii] and sameDesc[ii] and sameFill[ii] and sameExp[ii]
  Live' = Live
  Retired' = Retired
  othersUnchanged[ii]
}

// ── fill intent (operator asserts / releases the "as originally intended" condition — D16) ─────
/** Seal — the operator asserts the item is in its as-originally-intended condition (→ SEALED). Legal
    on any non-empty item (OPEN→SEALED; idempotent on SEALED); a later quantity-changing op demotes it
    back to OPEN. No quantity / identity / admin change. The positive-intent twin of consume-to-zero's
    EMPTY husk: a recognizable resting state, here an explicit assertion rather than a side effect. */
pred seal[ii: InventoryItem] {
  ii in Live
  ii.fillState != EMPTY                                          // else Rejected:Empty (nothing to seal)
  ii.fillState' = SEALED
  sameQty[ii] and sameLots[ii] and sameLoc[ii] and sameAdmin[ii] and sameDesc[ii] and sameExp[ii]
  Live' = Live
  Retired' = Retired
  othersUnchanged[ii]
}

/** Unseal — release the as-intended assertion (SEALED → OPEN) without touching the quantity. */
pred unseal[ii: InventoryItem] {
  ii in Live
  ii.fillState = SEALED                                          // else Rejected:NotApplicable
  ii.fillState' = OPEN
  sameQty[ii] and sameLots[ii] and sameLoc[ii] and sameAdmin[ii] and sameDesc[ii] and sameExp[ii]
  Live' = Live
  Retired' = Retired
  othersUnchanged[ii]
}
