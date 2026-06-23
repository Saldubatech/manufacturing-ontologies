# Working with the Alloy models — `alloy/`

Agent + contributor guide for the Alloy side of the manufacturing-ontologies
project. The Alloy models are the **behavioral / dynamic** counterpart to the OWL
ontology in `../owl/` (which is static structure + IOF/BFO alignment).

## Files

| File | Role |
|---|---|
| `kanban.als` | Root model — open/execute this. `module KanbanManufacturingSystem`; `open resource`. Stations, Resources' subtypes (Equipment/Personnel/Loop), KanbanCard, Job, InventoryLot, the 8-state lifecycle, operations, and the project's `run`/`check` commands. |
| `resource.als` | `module resource` — the `Resource` sig + ITU-T X.731 state vectors (operational/usage/administrative) + `ResourceStateInvariants` + its own `check`. Self-contained and independently analysable. |
| `../alloy-sample/` | Archived placeholder scaffolding (multi-file modular example). Not live. |

## Running the Analyzer

The tools are **Alloy 6.2** and **ROBOT 1.9.10** (needs Java; Corretto 21 is installed).
They are not committed — fetch them, pinned + checksum-verified, into the
git-ignored `tools/` dir. The fetch reuses `~/tools/{alloy,robot}/*.jar` if already
present (no re-download), otherwise downloads the pinned release.

### Make targets (preferred — run from the repo root, one dir up)

| Target | What it does |
|---|---|
| `make tools` | Fetch/verify Alloy + ROBOT into `tools/` (reuses `~/tools` if matching). Other targets depend on this and auto-run it. |
| `make alloy` | Launch the Alloy Analyzer **GUI** (then File→Open `alloy/kanban.als`). |
| `make check-alloy` | Headlessly run **every command in every `alloy/*.als`** and print SAT/UNSAT per command. Use this to validate after edits. |
| `make check-owl` | Validate `owl/kanban.ttl` loads its full import closure (ROBOT/OWLAPI). |
| `make check` | `check-alloy` + `check-owl`. |

### Direct jar invocation (equivalent; jar path is `tools/alloy.jar` after `make tools`)

```bash
java -jar tools/alloy.jar exec -c "*" -f alloy/kanban.als            # run all commands in a module
java -jar tools/alloy.jar -D info exec -c "*" -f alloy/resource.als  # -D info shows SAT/UNSAT per command
```

(`~/tools/alloy/alloy.jar` also works as a fallback if `make tools` hasn't run.)

- `exec` writes a `<stem>/receipt.json` (the full sig/field schema — a metamodel dump). Delete the dir after; it is git-ignored (`.gitignore` lists `/kanban/`, `/resource/`, etc.). `make check-alloy` cleans these for you.
- **Interpreting results**: a `run` that is **SAT** = instance found (good, and viewable). A `check` that is **UNSAT** = no counterexample = the assertion **holds** (good). UNSAT `run` = over-constrained/empty.
- **GUI** (`make alloy`, or `java -jar tools/alloy.jar` with no args): Execute menu has per-command entries plus **Show Metamodel** (⌘M, static schema diagram), **Show Latest Instance** (⌘L), **Show Parse Tree** (⌘P). After a SAT `run`, **Show** opens the Visualizer; for temporal (`var`) models step the trace with **Prev/Next state**. **Projection** slices the view over a chosen sig; **Theme** lists every sig/relation and controls styling.

## Project conventions

- **One concern per module** (`resource`, `kanban`, …); lower-level/shared concerns at the bottom, `open` only downward, no cycles.
- **Pattern (a): every module self-tests.** A concern module carries its own `fact` invariants *and* its own `assert`/`check` commands, and must be analysable standalone (open it directly to run its checks). `resource.als` is the template. The root (`kanban.als`) additionally holds whole-system commands.
- **Same-directory `open`s only** (`open resource`, not `open modules/a/b`). Deep paths trigger module-resolution friction. Use qualified names (`resource/Resource`) only on clashes.
- **Be sparing with global `fact`s** in reusable modules — a fact constrains every instance unconditionally and can mask inconsistency. Prefer predicates invoked by commands for optional/scenario constraints; reserve facts for inviolable structure.
- **Consider splitting static schema from dynamic behavior** as modules grow (sigs in one module, `var` fields + transition predicates in another).
- **Reuse `util/*`** (`util/ordering`, `util/integer`, `util/relation`, …); don't hand-roll.
- **Parameterize for reuse**: `module statemachine[S]` … `open statemachine[KanbanCard]`.

## Gotchas (all hit in practice — check these first)

1. **Identifiers cannot contain `-`** (hyphens). Module/sig/field names use `_` or camelCase even if the filename has hyphens.
2. **Commands run only from the opened ROOT module.** `run`/`check` in an `open`ed module do **not** execute from the root — open that module directly to run them. (This is why pattern (a) requires each module be standalone-analysable.)
3. **Scope must exceed the atoms a predicate forces.** Sigs sharing an abstract supertype share the scope; e.g. `run` needing 5 distinct entities under one abstract parent is UNSAT at `for 4`. Raise the scope or scope sigs individually (`for 4 but 8 Int`).
4. **Don't scope a `one sig`.** `... but 3 SomeOneSig` is an error — `one` already fixes it at 1.
5. **Open the root, not a submodule, in the GUI.** Hovering over an `open` line can print a harmless `/private/var/.../T/...als (No such file)` tooltip stack trace — cosmetic; execution resolves relative to the opened root's directory.
6. **`Int`/`String` appear in menus/projection** because built-ins are in scope (e.g. `capacityLimit: Int`); usually not worth projecting over.

## Relationship to `../owl/`

Same domain, complementary lenses: OWL/Protégé answers "is it consistent / how does it classify (under IOF/BFO)?"; Alloy answers "can this scenario occur / does an invariant ever break (within a finite scope)?". Keep the two in rough conceptual sync, but they are independent artifacts — Alloy has no IOF/BFO/QUDT imports.
