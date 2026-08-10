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

## v1 cost data (the evidence for the retune)

Uniform +2–3 census, glucose, one JVM/core each: global lattice row (mock-only cone)
~4h15m; kanban pair ~9h40m; order quad ~28h; demand `holdingProvenance` ~40h;
receiving `capturedFactsFrozen` ~30h — implementation cones pay tenant × item × depth ×
breadth simultaneously. Mock-composition roots are an order of magnitude cheaper than
implementation roots at comparable entity census (translation dominates: >1h CNF
translation observed on the implementation cones).

## Operational shape (target)

- `alloy/soak/tests/` splits into LEMMA roots (isolation, item agreement, binding
  soundness, Σ) and SLICED per-family roots; each sliced root's header carries its
  slice facts + justifications.
- Profiles: FULL (this catalog at generous axis scopes — design gates / monthly);
  OVERNIGHT (+1-notch sliced census — the schedulable default). `make soak` should gain
  a PAR fan-out like the gate (the v1 sequential form wasted the idle machine — fixed
  by hand mid-run, 2026-08-08).
