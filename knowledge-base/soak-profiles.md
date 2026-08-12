# Soak profiles: lemma-then-slice (assume-guarantee decomposition of the soak census)

Context: the first soak run (2026-08-08/09, the v1 uniform +2–3 census) proved 9+ widened
checks green but cost 4h–45h PER CHECK on the implementation cones — the uniform census
pays for the PRODUCT of every variety axis when each law's counterexamples can use only a
few. The retune design (MP + coordinator, 2026-08-09): factor the universe along
near-orthogonal concerns — prove each concern ONCE as its own widened LEMMA, then let
every domain-law soak run in a universe with that concern sliced out.

## The pattern

1. **Lemma root:** the cross-cutting concern's laws checked at GENEROUS variety on that
   axis (and lean everywhere else).
2. **Sliced roots:** every other law family adds a slice FACT collapsing the axis, with a
   recorded one-line justification of why the law's counterexamples cannot need it.
3. **Soundness is an argument, not a theorem the solver checks:** the composition
   ("violated in some universe ⇒ violated in a sliced universe, given the lemma") is
   assume-guarantee reasoning we RECORD per root. A law where the axis is load-bearing
   stays unsliced by construction — when in doubt, don't slice.

## The axis catalog (2026-08-09)

| Axis | Lemma (prove wide, once) | Slice (everywhere else) | Justification shape |
|---|---|---|---|
| **Tenancy** | kernel isolation + per-module `RForeignRef` guard laws, 3–4 tenants | `all a, b: Scoped \| a.tenantId = b.tenantId` | domain laws quantify within subjects' logs; tenancy touches them only through guards the lemma discharges |
| **Item agreement** (MP, 2026-08-09) | the EXISTING agreement family at 2–3 Items: `attachItemAgrees` (C3b), `receiveSameItemPool` (C4), kanban homogeneity (`RPoolWrongItem`, DT-015 R1), demand denomination | `one Item` in every operational-chain root (card/cycle/demand/order-line/receiving-line/attribution/delivery/production) | with one Item every classifier agrees by construction; wrong-item branches are dead; the chains' laws are about state/choreography, not classification |
| **Committed-only** | — (definitional: a refused occurrence has no post and is invisible to every LOCF read) | `all o: Occurrence \| committed[o]` in effect/frame/freeze/provenance roots | those laws quantify over committed occurrences + record reads; refusal atoms cannot appear in their counterexamples. NEVER slice reason-precision (refusals are its subject — but those are cheap SAT witnesses, not UNSAT proofs) |
| **Supplier/affiliate** | binding-soundness + role/tenancy guards at 2–3 affiliates/roles | 0–1 affiliates in operational roots | operational laws read bindings opaquely; soundness is guard-discharged |
| **Locator** | receiving's normative-locator semantics (its own root) | 1 PhysicalLocator, minimal Labels elsewhere | the locator is inert payload outside receiving §8.2.1 |
| **Depth vs breadth** | — (a profile split, not a lemma) | freeze/monotone/terminal families: Tick/Snapshot DEEP, entities few; exclusivity/provenance rows: entities BROAD, time shallow | a law's counterexample needs long chains OR many holders, not both |
| **Arithmetic** | Σ-law family with rich Quantity/Scalar | minimal Quantity/Scalar in structural-law roots | structural counterexamples don't compute |
| **Dense traces** (CAUTION) | — | `#Tick = #Occurrence`-style packing for OCCURRENCE-indexed laws only | UNSOUND for t-indexed laws (`all t: Tick …` — lattice rows, terminal closures: idle ticks are where LOCF drift would show). Per-family only; never global |
| **Inert values** (Note-class) | — (definitional: the laws read only presence/equality — no field, no inter-atom relation, no content) | `2 Note` everywhere a note-bearing cone is checked (1 to exist + 1 to witness replace-with-different; add/remove need only 1); NEVER default-scoped | a counterexample can differ in a note field in exactly three ways — add, remove, replace — and 2 atoms exhibit all three. Structural companion (2026-08-10): `Note` lives in its own `shared/note` module opened only by consumers, so non-note cones carry ZERO Note atoms instead of the default scope |

## v1 cost data (the evidence for the retune)

Uniform +2–3 census, glucose, one JVM/core each: global lattice row (mock-only cone)
~4h15m; kanban pair ~9h40m; order quad ~28h; demand `holdingProvenance` ~40h;
receiving `capturedFactsFrozen` ~30h — implementation cones pay tenant × item × depth ×
breadth simultaneously. Mock-composition roots are an order of magnitude cheaper than
implementation roots at comparable entity census (translation dominates: >1h CNF
translation observed on the implementation cones).

**REALIZED at DT-023 cut 7c (2026-08-11):** the lemma-then-slice shape is now BUILT for
reference data — `soak/lemmas/reference_data_dynamics.als` is the version-dynamics LEMMA
root (lifecycle shapes wide, current-uniqueness, pinned-vs-floating divergence), and all
six operational soak roots carry the CREATED-ONLY slice fact (each reference-data subject
= exactly its Create) with the lemma as justification.

**DT-023 cut 7a data point — census growth can DEMOTE a unit-tier check to soak-class:**
`unit_rcv_contract_linePoolExclusive` (the §8.5.3 lattice row at UNIT scopes) solved in
minutes at cuts 5/6 but blew past 9h CPU once the item log (`ItemOcc`/`ItemState`) rode
the receiver cone via the pin re-point. Relocated verbatim to
`soak/sliced/receiver_pool_exclusive.als` (`soak_rcv_linePoolExclusiveUnitScope`) — tier
change only. Watch the other multi-holder exclusivity checks for the same cliff as 7b/7c
widen the reference-data cones.

## Operational shape (BUILT 2026-08-11 — the DT-024 §6 chunked runner)

- The tree split is REALIZED: `alloy/soak/lemmas/` (one root per catalog axis with a
  lemma — reference_data_dynamics today; isolation/item-agreement/binding-soundness/Σ
  to come) and `alloy/soak/sliced/` (per-family roots incl. the demoted checks); each
  sliced root's header carries its slice facts + justifications (A-XX obligation).
- `make soak-chunk WINDOW=16h [PAR=n] [LENIENT=1] [RESUME=soak/<tag>]` — the
  night-window runner (`tools/soak-chunk.sh`): batch dir `soak/<YYYYMMDD-HHMM>/`
  (rejected on conflict), heaviest-first dispatch under a 2x margin (unknown estimate
  needs >4h remaining), per-command atomic completion, lenient over-runs surfaced at
  window end for the human kill/extend call. `make soak-status` folds the batch into
  `ledger.tsv`. Estimates: `alloy/soak/estimates.tsv`, keyed by scope-hash — the pre-cut-8
  measurements above are all INVALID (cones changed); the first batches remeasure.
- Profiles: FULL (this catalog at generous axis scopes — design gates / monthly);
  OVERNIGHT (+1-notch sliced census — the schedulable default via soak-chunk).

**A KILLED gate has performed NO verification (2026-08-11 lesson):** `check-alloy-par`'s
per-root "== X done" lines prove nothing — `run-root.sh` logs "done" on PARSE FAILURES
too (a root with a syntax error produces a log with zero solver verdicts and a clean-
looking done line). The gate's verdict lives ONLY in its final scan loop (missing-log
count, no-SAT/UNSAT-output, "against expectation", `[main] ERROR`). If a gate is killed
before that loop, re-run the scan manually over `out/par/*.log`; an interim grep must
include the parse-failure patterns (`Syntax error`, `[main] ERROR`), not just
expectation mismatches. (How the 7b `s.supplier.vendorRef` straggler survived one killed
gate and a five-JVM re-run scored from incomplete patterns.)
