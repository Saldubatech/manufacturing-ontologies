# Manufacturing Ontologies — Agent Instructions

Formal, machine-checked models of manufacturing/logistics systems. The primary artifact
is the **Alloy** behavioral / model-finding model under `alloy/`; `owl/` is a read-only
reference cache of the public standard ontologies (BFO 2020, IOF Core, QUDT); archived
spikes live in `alloy-sample/` (not in the gate).

## On session start

1. Read this file.
2. Touching `alloy/`? Read `alloy/CLAUDE.md` — the canonical structural guide (module
   anatomy, layer law, profiles, naming, tests, gotchas). Do not duplicate it here.
3. Read the `knowledge-base/` notes relevant to the area you are working in.
4. Skim the `Makefile` target comments — they carry operational rulings (solver choice,
   tier semantics, lint rationale), not just recipes.

## Design authority and provenance

- The model **implements rulings**, it does not originate them. Design happens in the
  companion workbook notebook `domain-ontology` (design topics `DT-XXX`, the rolling
  §-rulings, the work-board). Model changes that embody a ruling cite the topic in the
  commit subject — follow the existing log style
  (`inventory_pool R2: port the membership log onto the subject_log spine (DT-015)`).
- The workbook is a **private** repository. Teammates working here may not have access:
  the repo must stay self-sufficient — glossary doc-comments on every sig, contract-file
  headers stating each law's consistency class, and `knowledge-base/` notes carry the
  shareable distillation. Never make understanding a checked-in file depend on a
  workbook-only document.
- Rulings are **working hypotheses, not axioms**. Re-ruling is legitimate; its cost is
  the consistency re-check of everything built on the old ruling (suites, contracts,
  downstream modules), never an authority argument. When a change reverses a recorded
  ruling, say so explicitly in the commit message.

## Verification norms

- **`make check-alloy` is THE gate** — run it (green) before every push. It includes the
  layering lint. `make check-units` is the dev loop; `make check-affected` is a
  cone-aware shortcut and is **not sufficient for a push**.
- **Co-change rule (STRICT):** every model change ships with its verification changes in
  the same change set — commands/`expect`s in the affected roots, and the verification
  catalog trued. A model edit that changes verified behavior without touching its suites
  is an incomplete change. New modules land with a suite.
- `make check-examples` must stay green when `meta/` changes — the cookbook is part of
  the meta contract.
- `out/` is generated solver output — gitignored, never committed, wiped by
  `make clean`. Tools (`tools/*.jar`) are fetched pinned + checksum-verified by
  `make tools`, never committed.

## Conventions

- **Naming:** snake_case for everything under `alloy/` (Alloy module paths forbid `-`
  and `.` — see `alloy/CLAUDE.md`); kebab-case elsewhere in the repo. US English.
- **Git:** never push to `main` — work on project branches (`<user>/<project>`) and
  merge via PR unless explicitly directed otherwise.
- **`knowledge-base/`** holds repo-specific operational knowledge: one concrete pattern,
  gotcha, or decision per kebab-case file. Read the relevant notes before starting work;
  when you discover a non-obvious insight during a change, write it there **in the same
  change set**.

## Maintenance

Keep this file short and stable — it is the entry point, not the encyclopedia. Point to
canonical files (`alloy/CLAUDE.md`, `Makefile`, `knowledge-base/`); do not duplicate
their content. Update pointers when canonical files move.
