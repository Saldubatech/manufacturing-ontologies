module conventions/pinning_freezing/tests/pinning_freezing

open conventions/pinning_freezing/pinning_freezing

/*
 * Root for the PINNING/FREEZING exemplar (modeling-conventions §7). The cone is meta-only —
 * no machine vocabulary, no domain weight — so scopes stay tiny and fast.
 */

// ── the laws hold ───────────────────────────────────────────────────────────────────────────────
assert conv_pf_copyFrozen { copyFrozen }
check conv_pf_copyFrozen for 6 but 5 Int, 1 Vendor, 1 Doc, 9 Tick, 8 EntityId, 8 Snapshot expect 0

assert conv_pf_pinAgreesWithCopy { pinAgreesWithCopy }
check conv_pf_pinAgreesWithCopy for 6 but 5 Int, 1 Vendor, 1 Doc, 9 Tick, 8 EntityId, 8 Snapshot expect 0

// ── the laws are NOT vacuous: the full arc exists ───────────────────────────────────────────────
run conv_pf_commitArc {
  some v: Vendor, d: Doc, cm: CommitDocOcc, t: Tick | {
    committed[cm] and cm.subject = d
    resolve[docStateAt[d, t].dVendor] = v
    committedDocAt[d, t]
    some docStateAt[d, t].dCopy
  }
} for 6 but 5 Int, 1 Vendor, 1 Doc, 9 Tick, 8 EntityId, 8 Snapshot expect 1

// ── the headline WITNESS: the LIVE form drifts after a post-commit rename — the de-facto
// freeze violation that motivates the whole convention (LEGAL for a live read; the copy and
// the pin, read at the same t, still show the committed name). ─────────────────────────────────
run conv_pf_liveDrifts {
  some d: Doc, r: RenameOcc, t: Tick | {
    committed[r]
    committedDocAt[d, t]
    resolve[docStateAt[d, t].dVendor] = r.subject
    notAfter[r.tick, t]
    liveNameOf[docStateAt[d, t], t] != docStateAt[d, t].dCopy      // LIVE drifted…
    pinnedNameOf[docStateAt[d, t]]  = docStateAt[d, t].dCopy       // …PIN and COPY held
  }
} for 6 but 5 Int, 1 Vendor, 1 Doc, 2 Name, 10 Tick, 8 EntityId, 9 Snapshot expect 1

// ── and the LIVE form is CORRECT where currency is wanted: it tracks the rename ─────────────────
run conv_pf_liveTracksRename {
  some v: Vendor, r: RenameOcc, t1, t2: Tick | {
    committed[r] and r.subject = v
    precedes[t1, r.tick] and notAfter[r.tick, t2]
    some vendorNameAt[v, t1]
    vendorNameAt[v, t2] != vendorNameAt[v, t1]
  }
} for 6 but 5 Int, 1 Vendor, 0 Doc, 2 Name, 9 Tick, 6 EntityId, 6 Snapshot expect 1

// ── refusal sanity (reason-precise; the dedicated exemplar covers the idiom in depth) ───────────
run conv_pf_commitBeforeOpenRefused {
  some o: CommitDocOcc | refusedAtAdmission[o] and o.admission.because = RNotStarted
} for 5 but 5 Int, 0 Vendor, 1 Doc, 6 Tick, 5 EntityId, 5 Snapshot expect 1
