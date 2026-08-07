# The exclusivity lattice: genesis premise + integration-tier discharge

Context: the §8.5.3 pool-exclusivity rows (DT-020 cut 4, 2026-08-06). Three operational
findings for anyone extending the lattice (a new holder kind arrives owing its row).

## 1. The runtime mint enters the model as a NAMED PREMISE

Ownership-by-genesis says every holder kind MINTS its pool inside its own attach act, so a
fresh mint can never collide with an existing pool. The model cannot derive that — attach
kinds take caller-supplied pool refs. Rendering: a per-module premise pred
(`demandPoolGenesis`, `receivingPoolGenesis`) stating "no pool is named by two committed
attach acts" over the attach kinds the module can see, used as the ANTECEDENT of the
lattice row (`premise implies exclusivity`) — the groupAxioms/orderAxioms premise
mechanism, never a fact. A discipline breach stays representable (premise false; runtime
monitoring per PDEV-1424 catches it), and a weakened guard stays refusable. "Guard-and-
genesis-derived theorem" (§8.5.3's phrase) is literal: guard + premise ⊢ row.

## 2. Cross-kind rows need pool PROVENANCE in the peer contracts (published at cut 5)

The premise speaks about occurrence PAYLOADS; records are tied to payloads by the
implementations' EFFECTS (kanban: `sPool` = StartProcessing's pool; demand: `sHolding` =
StartProduction's holding). Until the peer contracts publish that provenance, a mock-tier
record may bind a pool no attach act named, and a row check finds a spurious
counterexample — at cut 4 this forced the rows' discharge to the integration tier (real
peers composed). **Cut 5 (MP ruling, 2026-08-06 evening) published the provenance laws**
(`poolProvenance` in kanban, `holdingProvenance` in demand — each a theorem of its
module's attach effect + frames, discharged in its own unit suite), after which:

- the row CHECKS live in their modules' UNIT suites (dev-loop regression coverage; the
  678s/82s integration-tier row checks left the gate — `demand_lattice.als` retired,
  `tests/integration/receiver.als` keeps the composed-arc witnesses);
- the rows stay in `guarantees` (mock-carried) — the §8.5.3 two-role rule;
- the whole-system row (`tests/pool_lattice.als`) is unchanged: check-only over the
  three MOCKS — a contract-composition validation, not an implementation discharge;
- the rule for the NEXT holder kind: its lattice row needs the provenance law of every
  kind visible below it; publish provenance the moment a row relies on it (L9), and give
  each publication its own card + unit discharge. Receiving publishes NO provenance law
  yet (no consumer relies on it).

## 3. Check scopes: pin the abstract parents or the check silently passes

A `for 5` check with pinned entity counts (2 Receiver + 3 ReceivingLine + tenant) can be
UNSATISFIABLE-BY-SCOPE: EntityId defaults to 5, `EntityIdIsKey` needs 6+, so the intended
universes never exist and the check "passes" over starved sub-universes. The receiving
suite's first run produced exactly this false pass on its lattice row (UNSAT at unit tier
where a genuine counterexample existed). Rule: every check pins `Occurrence`, `EntityId`,
`Tick`, `Snapshot` explicitly, sized from an atom census of the intended counterexample.
Lattice-row scope discipline: 2 of the OWN kind + 1 of each visible kind (the lower
kinds' same-kind pairs are their own rows' scopes); every check gets a SAT companion
against vacuity.

The DUAL failure mode hits SAT witnesses: the OVERALL `for N` bound still caps every
UNPINNED auxiliary sig (values, labels, handles), and a multi-holder witness quietly
exhausts one of them — the three-kind lattice companions were UNSAT at `for 6`/`for 8`
with generous explicit pins and SAT at `for 10` (bisected 2026-08-06: each holder pair
fits, the triple does not; the binding sig was not identified — the overall bound covers
it). Witnesses tolerate generous bounds (soundness is only at stake for checks), so when
a witness is inexplicably UNSAT, raise the OVERALL bound before hunting laws.
