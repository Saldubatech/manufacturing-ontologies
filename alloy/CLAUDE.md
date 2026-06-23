# Working with the Alloy model — `alloy/`

Agent + contributor guide for the Alloy side of the project. The model is the
**behavioral / model-finding** counterpart to the OWL ontology in `../owl/`. The
tree mirrors the system's **functional decomposition**.

## Structure & filing rule

- **Domain → directory, Module → file, one owning module per entity.** To add an
  entity, pick its single owning module and create/extend `<domain>/<module>.als`;
  reference other modules via `open`.
- **`meta/` is not a domain.** It holds modeling machinery:
  - `meta/kernel.als` — identity + the `Entity`/`Scoped` bound, `EntityId`, soft-ref `resolve`, cross-tenant isolation (DT-001.02, implemented).
  - `meta/values.als` — value objects: `Quantity` (amount+unit), `PhysicalLocator`; `Money`/`Duration` still opaque (QUDT bridge deferred, DT-002).
  - `meta/std/{bfo,iof,qudt}.als` — **vendored boundary stubs** copied from the OWL standards (MIREOT: only terms our entities touch, each with its source IRI). Currently STUBS; DT-002. OWL stays system-of-record.
  - `meta/state_machine/machine.als` — generic FSM framework reifying common-module's `StateEngine` (DT-003): `State`/`Signal`/`Guard`/`Transition`/`StateMachine` + once-stated well-formedness/determinism FACTS + checkable `allStatesReachable`/`liveSignals`/`firedInto`. Concrete machines extend `State`/`Signal` and pin a `StateMachine` atom.
  - `meta/x731_state/state.als` — ITU-T X.731 expressed via `meta/state_machine`: three region machines (Operational ∥ Usage ∥ Administrative) + `Resource` host + interlocks as cross-region invariants (DT-003).
- Domains: `system reference_data resources procurement shop_access fulfillment operations receiving shipping oam workflows_and_integrations`. Only `reference_data` (Item/ItemSupply/BusinessAffiliate/BusinessRole) and `resources` (KanbanCard) have content; the rest are stubbed (`.gitkeep`).
- The original throwaway X.731 behavioral spike (Loop/Station/Operator/Job/InventoryLot + 8-state lifecycle) was archived to `../alloy-sample/kanban_sim/` when the real code-faithful `KanbanCard` landed (DT-001.08). It is not in the `make check-alloy` set; see its README.

## ⚠️ Naming: snake_case, never `-` or `.`

Alloy module names cannot contain `-` or `.` (both are **syntax errors**), and the
`module <path>` declaration **must equal the file's path under `alloy/`** (Alloy
strips it to compute the project root, then resolves every `open` from there).
Therefore:

- Directories and files use **snake_case** (`reference_data/`, `kanban_card.als`),
  even though the functional domain canonical names are kebab-case
  (`reference-data` ↔ `reference_data`). This overrides the workspace kebab-case
  convention **inside `alloy/` only**.
- Every file declares `module <path-under-alloy>` (e.g. `module resources/loop`,
  `module resources/tests/kanban`, `module meta/std/iof`).
- `open` uses paths-from-`alloy/`: `open meta/util`, `open resources/loop`.

## Library vs. root (where commands live)

- **Library files** (`meta/…`, `<domain>/<module>.als`) carry all model-defining
  elements: `sig`, `fact`, `fun`, and co-located checkable `assert`/`pred`.
- **Only root files carry `run`/`check`.** A root does **not** execute commands
  from the modules it opens. Roots are the `tests/*.als` files.
- Open a **root** in the GUI / pass it to `exec`; never a library module.

## Tests & command tiers

- Tests live in a **`tests/` subdirectory** of each modeling directory (NOT
  `*.test.als` — dotted module names are illegal). Per-module suite
  `<domain>/tests/<module>.als`; domain-aggregate `<domain>/tests/aggregate.als`;
  whole-system `tests/system.als`.
- **Command-name tiers** (for wildcard selection): `unit_*` (module), `dom_*`
  (domain aggregate), `sys_*` (system). New commands follow this; relocated
  commands kept their original names (`showSimulation`, `X731Consistency`).
- **No master root** aggregates suites — the Makefile iterates `tests/` roots.

## Running

From the repo root: `make check-alloy` (all), `make test-unit`, `make test-sys`,
`make alloy` (GUI). Direct: `java -jar tools/alloy.jar exec -c "<name|glob|*>" -o /tmp/ao -f <root>.als`.
Interpreting: `run` SAT = instance found; `check` UNSAT = assertion holds.

## `fact` vs `assert` vs `pred`

- `fact` — inviolable structural invariant, always enforced (use sparingly).
- `assert`+`check` — property to verify (counterexample if wrong); most tests.
- `pred`+`run` — scenario existence / "this works".

## Gotchas

1. **No `-` or `.` in module names** (snake_case; see above).
2. **Commands run only from the opened root**; library `run`/`check` won't fire.
3. `module <path>` must match the file's path under `alloy/`.
4. Scope must exceed the atoms a predicate forces (shared abstract supertypes
   share the scope); don't put a numeric scope on a `one sig`.
5. Open a root, not a submodule, in the GUI.
6. **Reified state machines (DT-003) need explicit per-sig scopes.** `State`/
   `Signal` are abstract and fully partitioned into `one sig`s, and the no-orphan
   facts pin `Transition`/`Guard`, so each command must size those families exactly
   (e.g. kanban: `but 16 State, 20 Signal, 20 Transition, 2 StateMachine, 0 Guard`).
   `sig` is a reserved keyword — never a variable name (use `sg`).

## Pointers

Canonical structure spec + rationale: workbook notebook `domain-ontology` →
`alloy-repository-structure.md`, `threads/dt-001-alloy-directory-structure.md`
(layout, DT-001.01 decided), `threads/dt-002-bridging-owl-standard-models.md`
(vendoring), `modeling-conventions.md` (DAG/aggregation/refs/tight-by-default),
`reference-data-entities.md` + `kanban-cards-entities.md` (code-authoritative entity
inventories). `meta/kernel` is implemented; the reference_data slice and the
code-faithful `KanbanCard` are modeled. Next: populate `meta/std` (DT-002), enrich
fields, and decide the event-history/bitemporal depth (DT-001.03).
