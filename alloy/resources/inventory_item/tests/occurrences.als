module resources/inventory_item/tests/occurrences

open resources/inventory_item/occurrences

/*
 * Suite for the InventoryItem OCCURRENCE LOG (DT-006 domain build). The cone is fully STATIC — the
 * canonical entity is identity-only (DT-011; the var carrier lives in legacy/). Premises as in
 * every quantitative root. Scope notes: each committed occurrence consumes a Tick + record +
 * Quantity atoms — scopes size those families generously and keep the rest small.
 */
fact ScalarPremises { groupAxioms and orderAxioms }   // group suffices: domain roots do additive arithmetic only (DT-011)

// ── SAT witnesses ─────────────────────────────────────────────────────────────────────────────────
// A committed Create: read back through the projections — live, with its born record.
run unit_occ_createReadsBack {
  some o: CreateOcc | committed[o]
    and liveAt[o.target, o.tick]
    and stateAt[o.target, o.tick] = o.post
    and o.post.sActual = o.qty
} for 5 but 3 Scalar, 5 Int expect 1

// A committed chain create → replenish → consume on one item, each reading the prior record.
run unit_occ_lifecycleChain {
  some ii: InventoryItem, c: CreateOcc, r: ReplenishOcc, k: ConsumeOcc | {
    c.target = ii and r.target = ii and k.target = ii
    precedes[c.tick, r.tick] and precedes[r.tick, k.tick]
    committed[c] and committed[r] and committed[k]
    r.pre = c.post and k.pre = r.post
    stateAt[ii, k.tick] = k.post
  }
} for 6 but 3 Scalar, 5 Int, 8 Quantity expect 1

// An overdraw is REFUSED with exactly ROverdraw (reason-precise witnessing).
run unit_occ_overdrawRefused {
  some o: ConsumeOcc | refusedAtAdmission[o] and o.admission.because = ROverdraw
} for 5 but 3 Scalar, 5 Int expect 1

// Resurrection is REFUSED: a Create over a deleted item's history carries RAlreadyExists.
run unit_occ_resurrectionRefused {
  some d: DeleteOcc, c: CreateOcc | {
    committed[d] and d.target = c.target and precedes[d.tick, c.tick]
    refusedAtAdmission[c] and RAlreadyExists in c.admission.because
  }
} for 5 but 3 Scalar, 5 Int expect 1

// A committed Split exists: both sides' records produced, the new item live, the origin still live.
run unit_occ_splitProjects {
  some o: SplitOcc | committed[o]
    and liveAt[o.nu, o.tick] and liveAt[o.target, o.tick]
    and stateAt[o.nu, o.tick] = o.nuPost
} for 6 but 3 Scalar, 5 Int, 8 Quantity expect 1

// A committed Merge retires the absorbed item and keeps the survivor live.
run unit_occ_mergeRetiresAbsorbed {
  some o: MergeOcc | committed[o]
    and liveAt[o.target, o.tick] and not liveAt[o.absorbed, o.tick]
} for 6 but 3 Scalar, 5 Int, 8 Quantity expect 1

// ── theorems (check; UNSAT = holds) — invariants DERIVED from the witnessed guards ───────────────
// No committed consume overdraws (the guard, seen from the projection side).
assert unit_occ_noCommittedOverdraw {
  all o: ConsumeOcc | committed[o] implies gWithin[o.amount.byUnit, o.pre.sAvailableQty]
}
check unit_occ_noCommittedOverdraw for 5 but 3 Scalar, 5 Int expect 0

// LPN terminality: a committed Create never lands on an item with ANY committed history
// (delete tombstones included — no resurrection).
assert unit_occ_noResurrection {
  all o: CreateOcc | committed[o] implies no priorOn[o, o.target]
}
check unit_occ_noResurrection for 5 but 3 Scalar, 5 Int expect 0

// Once retired, an item is never live again (terminal retirement, via the guards).
assert unit_occ_terminalRetirement {
  all ii: InventoryItem, t1, t2: Tick |
    (notAfter[t1, t2] and some lastTouch[ii, t1] and not liveAt[ii, t1]) implies not liveAt[ii, t2]
}
check unit_occ_terminalRetirement for 5 but 3 Scalar, 5 Int expect 0

// CONSERVATION over Split: the origin's read quantity equals remainder + split-off (needs the ring
// premise — add/negate cancellation).
assert unit_occ_splitConserves {
  all o: SplitOcc | committed[o] implies
    o.pre.sActual.byUnit = add[o.post.sActual.byUnit, o.nuPost.sActual.byUnit]
}
check unit_occ_splitConserves for 5 but 3 Scalar, 5 Int, 8 Quantity expect 0

// CONSERVATION over Merge: the survivor's produced quantity is the sum of the two read quantities.
assert unit_occ_mergeConserves {
  all o: MergeOcc | committed[o] implies
    o.post.sActual.byUnit = add[o.pre.sActual.byUnit, o.absPre.sActual.byUnit]
}
check unit_occ_mergeConserves for 5 but 3 Scalar, 5 Int, 8 Quantity expect 0

// ── parity tranche (from the legacy lifecycle/ops checklists) ─────────────────────────────────────
// Seal is re-enterable (D16): seal → unseal round-trip, quantity untouched, fill back to OPEN.
run unit_occ_sealUnsealRoundTrip {
  some ii: InventoryItem, sl: SealOcc, us: UnsealOcc | {
    sl.target = ii and us.target = ii and precedes[sl.tick, us.tick]
    committed[sl] and committed[us] and us.pre = sl.post
    us.post.sFill = OPEN and us.post.sActual = sl.pre.sActual
  }
} for 6 but 3 Scalar, 5 Int, 8 Quantity expect 1

// A lock blocks consumption: a consume after a committed Lock is refused with exactly RLocked.
run unit_occ_lockBlocksConsume {
  some ii: InventoryItem, l: LockOcc, k: ConsumeOcc | {
    l.target = ii and k.target = ii and precedes[l.tick, k.tick]
    committed[l] and refusedAtAdmission[k] and k.admission.because = RLocked
  }
} for 6 but 3 Scalar, 5 Int, 8 Quantity expect 1

// Deplete-vs-delete (the D-rule): consume-to-zero leaves the item LIVE and revivable by Replenish.
run unit_occ_depleteThenRevive {
  some ii: InventoryItem, k: ConsumeOcc, r: ReplenishOcc | {
    k.target = ii and r.target = ii and precedes[k.tick, r.tick]
    committed[k] and committed[r]
    k.post.sFill = EMPTY and liveAt[ii, k.tick]
    r.pre = k.post and r.post.sFill != EMPTY
  }
} for 6 but 3 Scalar, 5 Int, 8 Quantity expect 1

// D17 as a theorem: no committed operation ever LENGTHENS an expiry (creates aside — they set it).
assert unit_occ_expiryNeverLengthens {
  all o: IIOcc - CreateOcc | committed[o] implies
    (some o.pre.sExpiration implies (some o.post.sExpiration and o.post.sExpiration <= o.pre.sExpiration))
}
check unit_occ_expiryNeverLengthens for 5 but 3 Scalar, 5 Int expect 0

// D16 as a theorem: SEALED is entered ONLY by Seal — no other committed kind transitions into it.
assert unit_occ_sealedOnlyBySeal {
  all o: IIOcc - SealOcc | committed[o] implies
    not (o.post.sFill = SEALED and o.pre.sFill != SEALED)
}
check unit_occ_sealedOnlyBySeal for 5 but 3 Scalar, 5 Int expect 0

// ── the Quantity-reframing tranche (2026-07-02): partiality + the valid-UoM rule ──────────────────
// An INCOMPARABLE consume (amount on a different unit basis) is refused with exactly RIncomparable —
// the conservative-refusal convention, distinct from a provable overdraw.
run unit_occ_incomparableRefused {
  some o: ConsumeOcc | refusedAtAdmission[o] and o.admission.because = RIncomparable
} for 5 but 3 Scalar, 5 Int expect 1

// DT-009's valid-UoM rule: a TRACKED item's operation using a unit outside its scheme is refused
// carrying RInvalidUnit.
run unit_occ_invalidUnitRefused {
  some o: ConsumeOcc | refusedAtAdmission[o] and RInvalidUnit in o.admission.because
    and some schemeOf[o.target]
} for 5 but 3 Scalar, 5 Int expect 1

// The rule as a theorem: committed operations on tracked items use only scheme units.
assert unit_occ_committedUnitsValid {
  all o: ConsumeOcc | committed[o] implies unitsOk[o.amount.byUnit, o.target]
}
check unit_occ_committedUnitsValid for 5 but 3 Scalar, 5 Int expect 0
