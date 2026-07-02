module resources/inventory_item/transitions

/*
 * VALUE-PARAMETERIZED TRANSITION CORES for the InventoryItem operations (DT-006 bridge layer 1:
 * one shared spec, any carrier). Each core relates PRE field values to POST field values plus the
 * operation's parameters — no commitment to where the values come from: the `var` model
 * instantiates them with `ii.f` / `ii.f'`, the occurrence log with `o.pre.sF` / `o.post.sF`.
 *
 * Quantities are passed at the MAP level (`Unit -> lone Scalar`): the empty map IS the keyed zero,
 * which uniformly encodes the `lone Quantity` absent case (an absent degradedQty joins to the empty
 * map on either carrier). Enum/lot/expiration fields pass as plain values. GUARDS are not here —
 * value-level guard checks are (see the g* preds); carrier-specific guard packaging (var
 * preconditions; log reason-precise witnessing) lives with each carrier.
 *
 * Staged per DT-006 #4: the quantity/degraded writers. The pure state/descriptive writers
 * (lock/unlock, seal/unseal, move, adjustProperties) follow mechanically later.
 */

open shared/values                             // Quantity maps, Unit
open meta/keyed_value_algebra/keyed_order      // classify, lte, isZero, semanticEq (+ add, negate, zero)
open resources/inventory_item/inventory_item   // FillState, AdministrativeState, LotNumber enums/handles

/** minExpV — the earlier of two expirations; ABSENT = "never" = +∞ (D17). */
fun minExpV[a, b: lone Int]: lone Int { no a => b else (no b => a else (a < b => a else b)) }

/** fillAfter — D16: a real-quantity change lands in OPEN, or EMPTY when the new on-hand is zero. */
fun fillAfter[actA: Unit -> lone Scalar]: one FillState { isZero[actA] => EMPTY else OPEN }

// ── value-level guard checks (shared vocabulary for both carriers' guards) ───────────────────────
pred gPositive[m: Unit -> lone Scalar]     { classify[m] = POSITIVE }
pred gNonNegative[m: Unit -> lone Scalar]  { classify[m] in (ZERO + POSITIVE) }
pred gWithin[m, bound: Unit -> lone Scalar] { lte[m, bound] }
pred gAllOf[m, whole: Unit -> lone Scalar] { semanticEq[m, whole] = EQUAL }

// ── effect cores ─────────────────────────────────────────────────────────────────────────────────
/** createE — born with qty, no qualifiers, OPEN, UNLOCKED, bare descriptors, given expiry. */
pred createE[qty: Unit -> lone Scalar, exp: lone Int,
             actA, degA: Unit -> lone Scalar, lotsA: set LotNumber, fillA: one FillState,
             adminA: one AdministrativeState, expA: lone Int] {
  actA = qty and no degA and no lotsA
  fillA = OPEN and adminA = UNLOCKED and expA = exp
}

/** replenishE — actual += delta; lots unioned; degraded kept; fill OPEN; expiry only shortens. */
pred replenishE[delta: Unit -> lone Scalar, lots: set LotNumber, exp: lone Int,
                actB, degB: Unit -> lone Scalar, lotsB: set LotNumber, expB: lone Int,
                actA, degA: Unit -> lone Scalar, lotsA: set LotNumber, fillA: one FillState, expA: lone Int] {
  actA = add[actB, delta]
  lotsA = lotsB + lots
  degA = degB
  fillA = fillAfter[actA]
  expA = minExpV[expB, exp]
}

/** consumeE — actual −= amount; consume-to-zero clears degraded + lots (husk); fill demotes. */
pred consumeE[amount: Unit -> lone Scalar,
              actB, degB: Unit -> lone Scalar, lotsB: set LotNumber,
              actA, degA: Unit -> lone Scalar, lotsA: set LotNumber, fillA: one FillState] {
  actA = add[actB, negate[amount]]
  (isZero[actA]) => (no degA and no lotsA) else (degA = degB and lotsA = lotsB)
  fillA = fillAfter[actA]
}

/** adjustQuantityE — set to observed count (non-conservative): actual' = good + degraded'; to-zero husks. */
pred adjustQuantityE[good, degIn: Unit -> lone Scalar, degWasGiven: one Int,   // 1 = observedDeg given, 0 = keep
                     degB: Unit -> lone Scalar, lotsB: set LotNumber,
                     actA, degA: Unit -> lone Scalar, lotsA: set LotNumber, fillA: one FillState] {
  let dmap = (degWasGiven = 1 => degIn else degB) |
  let amap = add[good, dmap] {
    actA = amap
    (isZero[amap]) => (no degA and no lotsA)
                   else (degA = dmap and lotsA = lotsB)
  }
  fillA = fillAfter[actA]
}

/** inspectE — set the worthiness driver; zero/absent clears; quantity untouched. */
pred inspectE[deg: Unit -> lone Scalar,
              actB: Unit -> lone Scalar, lotsB: set LotNumber,
              actA, degA: Unit -> lone Scalar, lotsA: set LotNumber, fillA: one FillState, fillB: one FillState] {
  actA = actB
  (isZero[deg]) => no degA else degA = deg
  lotsA = lotsB
  fillA = fillB                                  // D16: inspection preserves SEALED/OPEN
}

/** rePackE — re-express good/degraded in a new basis (caller-asserted); emptiness-preserving;
    lots + fill preserved (re-expression is not a real-quantity change). */
pred rePackE[gIn, dIn: Unit -> lone Scalar, gGiven, dGiven: one Int,
             actB, degB: Unit -> lone Scalar, lotsB: set LotNumber, fillB: one FillState,
             actA, degA: Unit -> lone Scalar, lotsA: set LotNumber, fillA: one FillState] {
  let dmap = (dGiven = 1 => dIn else degB) |
  let gmap = (gGiven = 1 => gIn else add[actB, negate[degB]]) |
  let amap = add[gmap, dmap] {
    lte[dmap, amap] and not isZero[amap]
    actA = amap
    (isZero[dmap]) => no degA else degA = dmap
  }
  lotsA = lotsB
  fillA = fillB
}

/** splitE — the two-sided conservation: new item born with the split-off portions (full lot copy,
    descriptor inheritance is carrier-side); the remainder loses them; either side may husk. */
pred splitE[soGood, soDeg: Unit -> lone Scalar,
            actB, degB: Unit -> lone Scalar, lotsB: set LotNumber,
            remAct, remDeg: Unit -> lone Scalar, remLots: set LotNumber, remFill: one FillState,
            nuAct, nuDeg: Unit -> lone Scalar, nuLots: set LotNumber, nuFill: one FillState] {
  let soTot = add[soGood, soDeg] {
    nuAct = soTot
    (isZero[soDeg]) => no nuDeg else nuDeg = soDeg
    nuLots = lotsB
    nuFill = fillAfter[nuAct]
    remAct = add[actB, negate[soTot]]
    (isZero[remAct]) => (no remDeg and no remLots)
      else { let rd = add[degB, negate[soDeg]] | (isZero[rd] => no remDeg else remDeg = rd)
             remLots = lotsB }
    remFill = fillAfter[remAct]
  }
}

/** mergeE — survivor absorbs: quantities + degraded sum, lots union, expiry min; fill demotes. */
pred mergeE[survActB, survDegB, absActB, absDegB: Unit -> lone Scalar,
            survLotsB, absLotsB: set LotNumber, survExpB, absExpB: lone Int,
            actA, degA: Unit -> lone Scalar, lotsA: set LotNumber, fillA: one FillState, expA: lone Int] {
  actA = add[survActB, absActB]
  let dsum = add[survDegB, absDegB] | (isZero[dsum]) => no degA else degA = dsum
  lotsA = survLotsB + absLotsB
  expA = minExpV[survExpB, absExpB]
  fillA = fillAfter[actA]
}
