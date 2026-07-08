module conventions/reason_precise_refusals/tests/reason_precise_refusals

open conventions/reason_precise_refusals/reason_precise_refusals

/*
 * Root for the REASON-PRECISE-REFUSALS exemplar. The suite DEMONSTRATES the check+witness
 * pairing discipline on itself: every check is followed by the SAT witnesses that prove the
 * universe it quantified over is inhabited (an over-constrained universe discharges any law
 * VACUOUSLY — the witnesses are the alarm; the 2026-07-08 order build caught a real instance
 * of exactly this with a contradictory `0 Item` pin).
 */

// ── the laws hold… ──────────────────────────────────────────────────────────────────────────────
assert conv_rpr_passRequiresOpen { passRequiresOpen }
check conv_rpr_passRequiresOpen for 6 but 5 Int, 1 Latch, 9 Tick, 6 EntityId, 8 Snapshot expect 0

assert conv_rpr_refusalsAreExact { refusalsAreExact }
check conv_rpr_refusalsAreExact for 6 but 5 Int, 1 Latch, 9 Tick, 6 EntityId, 8 Snapshot expect 0

// ── …NON-VACUOUSLY: the quantified populations exist ────────────────────────────────────────────
run conv_rpr_passArc {
  some l: Latch, p: PassOcc, t: Tick | {
    committed[p] and p.subject = l
    latchStatusAt[l, t] = L_OPEN2 and p in passesAt[l, t]
  }
} for 6 but 5 Int, 1 Latch, 8 Tick, 5 EntityId, 7 Snapshot expect 1

// ── one witness per Reason, each EXACT ──────────────────────────────────────────────────────────
run conv_rpr_alreadyInstalledExact {
  some o: InstallOcc | refusedAtAdmission[o] and o.admission.because = RAlreadyInstalled
} for 5 but 5 Int, 1 Latch, 6 Tick, 5 EntityId, 5 Snapshot expect 1

run conv_rpr_notInstalledExact {
  some o: OpenOcc | refusedAtAdmission[o] and o.admission.because = RNotInstalled
} for 5 but 5 Int, 1 Latch, 6 Tick, 5 EntityId, 5 Snapshot expect 1

run conv_rpr_shutExact {
  some o: PassOcc | refusedAtAdmission[o] and o.admission.because = RShut
} for 5 but 5 Int, 1 Latch, 7 Tick, 5 EntityId, 6 Snapshot expect 1

run conv_rpr_openMismatchExact {
  some o: OpenOcc | refusedAtAdmission[o] and o.admission.because = ROpen2
} for 5 but 5 Int, 1 Latch, 7 Tick, 5 EntityId, 6 Snapshot expect 1

// ── the MULTI-REASON refusal: `because` carries the WHOLE violation set ─────────────────────────
run conv_rpr_multiReasonCarriesAll {
  some o: PassOcc | {
    refusedAtAdmission[o]
    o.admission.because = RNotInstalled + RShut
  }
} for 5 but 5 Int, 1 Latch, 6 Tick, 5 EntityId, 5 Snapshot expect 1

// ── refusals are FIRST-CLASS on the log: a refused pass leaves the record untouched and the
// subject continues (a later committed pass succeeds) ───────────────────────────────────────────
run conv_rpr_refusalThenRecovery {
  some l: Latch, bad: PassOcc, op: OpenOcc, good: PassOcc | {
    refusedAtAdmission[bad] and committed[op] and committed[good]
    bad.subject = l and op.subject = l and good.subject = l
    precedes[bad.tick, op.tick] and precedes[op.tick, good.tick]
  }
} for 7 but 5 Int, 1 Latch, 10 Tick, 6 EntityId, 8 Snapshot expect 1
