module conventions/call_first_saga/tests/call_first_saga

open conventions/call_first_saga/call_first_saga

/*
 * Root for the CALL-FIRST SAGA exemplar (the B1 matrix's C/OP class). Meta-only cone; tiny
 * scopes.
 */

// ── the commit-gate law holds (a theorem of the guard — no enforcement facts) ───────────────────
assert conv_cfs_gate { activateRequiresHeld }
check conv_cfs_gate for 6 but 5 Int, 2 Slot, 2 Job, 9 Tick, 8 EntityId, 8 Snapshot expect 0

// ── the full saga arc exists (non-vacuity): acquire FIRST, then the commit ──────────────────────
run conv_cfs_sagaArc {
  some j: Job, s: Slot, a: AcquireOcc, v: ActivateOcc, t: Tick | {
    committed[a] and committed[v]
    a.subject = s and v.subject = j and resolve[v.slot] = s
    precedes[a.tick, v.tick]
    jobStatusAt[j, t] = J_ACTIVE and slotStatusAt[s, t] = S_HELD
    alignedAt[t]
  }
} for 6 but 5 Int, 1 Slot, 1 Job, 9 Tick, 8 EntityId, 8 Snapshot expect 1

// ── THE CRASH WINDOW IS LEGAL: peer leg committed, caller commit never landed ───────────────────
run conv_cfs_inFlightLegal {
  some s: Slot, t: Tick | {
    slotStatusAt[s, t] = S_HELD
    no v: ActivateOcc | committed[v]
    not alignedAt[t]
  }
} for 6 but 5 Int, 1 Slot, 1 Job, 8 Tick, 7 EntityId, 7 Snapshot expect 1

// ── CONVERGENCE BY COMPENSATION: the abandoned saga releases the peer leg ───────────────────────
run conv_cfs_compensation {
  some s: Slot, a: AcquireOcc, r: ReleaseOcc2, t: Tick | {
    committed[a] and committed[r]
    a.subject = s and r.subject = s and precedes[a.tick, r.tick]
    no v: ActivateOcc | committed[v]
    slotStatusAt[s, t] = S_FREE and notAfter[r.tick, t]
    alignedAt[t]
  }
} for 6 but 5 Int, 1 Slot, 0 Job, 9 Tick, 7 EntityId, 7 Snapshot expect 1

// ── the GATE refuses, reason-precisely, when the peer leg never ran ─────────────────────────────
run conv_cfs_gateRefused {
  some o: ActivateOcc | {
    refusedAtAdmission[o] and o.admission.because = RSlotNotHeld
    slotStatusAt[resolve[o.slot] & Slot, o.tick] = S_FREE
  }
} for 6 but 5 Int, 1 Slot, 1 Job, 8 Tick, 7 EntityId, 7 Snapshot expect 1

// ── RETRY CONVERGES: a refused first attempt, then the peer leg, then a committed retry ─────────
run conv_cfs_retryConverges {
  some j: Job, s: Slot, v1, v2: ActivateOcc, a: AcquireOcc | {
    refusedAtAdmission[v1] and committed[v2] and committed[a]
    v1.subject = j and v2.subject = j and a.subject = s
    resolve[v1.slot] = s and resolve[v2.slot] = s
    precedes[v1.tick, a.tick] and precedes[a.tick, v2.tick]
  }
} for 7 but 5 Int, 1 Slot, 1 Job, 10 Tick, 8 EntityId, 9 Snapshot expect 1
