module conventions/notification_convergence/tests/notification_convergence

open conventions/notification_convergence/notification_convergence

/*
 * Root for the NOTIFICATION-CONVERGENCE exemplar (the B1 matrix's C/NOTIF class). Meta-only
 * cone; tiny scopes.
 */

// ── the laws hold ───────────────────────────────────────────────────────────────────────────────
assert conv_nc_idempotent { reflectIdempotent }
check conv_nc_idempotent for 6 but 5 Int, 1 Source, 1 Mirror, 9 Tick, 7 EntityId, 8 Snapshot expect 0

assert conv_nc_sound { reflectSound }
check conv_nc_sound for 6 but 5 Int, 1 Source, 1 Mirror, 9 Tick, 7 EntityId, 8 Snapshot expect 0

// ── the settled arc exists (non-vacuity): ping → reflect → quiescent with content ───────────────
run conv_nc_settledArc {
  some m: Mirror, p: PingOcc, r: ReflectOcc, t: Tick | {
    committed[p] and committed[r]
    r.subject = m and r.ping = p
    precedes[p.tick, r.tick] and notAfter[r.tick, t]
    settledAt[m, t] and some seenAt[m, t]
  }
} for 6 but 5 Int, 1 Source, 1 Mirror, 9 Tick, 7 EntityId, 8 Snapshot expect 1

// ── THE MISSED-NOTIFICATION WINDOW IS LEGAL: emitted, not reacted, quiescence false ─────────────
run conv_nc_missedWindowLegal {
  some m: Mirror, p: PingOcc, t: Tick | {
    committed[p] and p.subject = resolve[m.watches]
    notAfter[p.tick, t]
    no r: ReflectOcc | committed[r]
    not settledAt[m, t]
  }
} for 6 but 5 Int, 1 Source, 1 Mirror, 8 Tick, 7 EntityId, 7 Snapshot expect 1

// ── SELF-HEAL RESTORES: the same reaction kind, driven late, re-establishes quiescence ──────────
run conv_nc_selfHealRestores {
  some m: Mirror, p: PingOcc, r: ReflectOcc, t1, t2: Tick | {
    committed[p] and committed[r]
    r.subject = m and r.ping = p
    notAfter[p.tick, t1] and precedes[t1, r.tick] and notAfter[r.tick, t2]
    not settledAt[m, t1]
    settledAt[m, t2]
  }
} for 6 but 5 Int, 1 Source, 1 Mirror, 10 Tick, 7 EntityId, 8 Snapshot expect 1

// ── the DUPLICATE is a typed no-op on the reaction's own log ────────────────────────────────────
run conv_nc_duplicateRefused {
  some o: ReflectOcc | refusedAtAdmission[o] and o.admission.because = RDuplicate
} for 6 but 5 Int, 1 Source, 1 Mirror, 9 Tick, 7 EntityId, 8 Snapshot expect 1
