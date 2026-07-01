# Working with the Alloy model — `alloy/`

Agent + contributor guide for the Alloy side of the project. The model is the
**behavioral / model-finding** model, grounded in the public standard ontologies cached
for reference in `../owl/` (BFO/IOF/QUDT — source-of-truth, not maintained here). The
tree mirrors the system's **functional decomposition**.

## Structure & filing rule

- **Domain → directory, Module → directory, one owning module per entity.** The
  **module** is the unit of modeling/development: each module is a directory
  `<domain>/<module>/` holding its definition/fact files (one per entity/concept,
  e.g. `reference_data/item/item.als` + `reference_data/item/item_supply.als`) and a
  `tests/` subdirectory. A child entity lives in its parent's module (ItemSupply in
  `item/`, BusinessRole in `business_affiliate/`). Module paths therefore carry the
  module segment: `module reference_data/item/item`, `open resources/kanban_card/kanban_card`.
- **Every defined concept carries a glossary doc-comment.** Immediately above each
  `sig`/`enum`, a `/** Term — one-line glossary definition. */` block (the
  type-level "description"; Alloy has no sig annotations, so this is the convention).
  It is inert to the analyzer and extractable (sig name → definition).
- **`meta/` is not a domain.** It holds modeling machinery:
  - `meta/kernel.als` — identity + the `Entity`/`Scoped` bound, `EntityId`, soft-ref `resolve`, cross-tenant isolation (DT-001.02, implemented).
  - `meta/values.als` — value objects: `Money` (Currency-keyed) and `Quantity` (Unit-keyed) are **instances of the keyed monoid** (`byCurrency`/`byUnit` normal-form maps, DT-005); `PhysicalLocator` (9-level). (`Duration` — ordered elapsed-time value type — lives in the standalone `meta/time/duration`; the instant→duration metric is in `meta/time`. DT-010. `keyed_sum` is now parameterized `keyed_sum[Node]`.)
  - `meta/std/{bfo,iof,qudt}.als` — **boundary stubs** MIREOT'd from the public standards (only terms our entities touch, each with its source IRI). Currently STUBS; DT-002. The standards (BFO/IOF/QUDT) stay source-of-truth as a **read-only reference cache** under `../owl/imports/` (consult via ROBOT) — we no longer maintain an authored OWL ontology; harvested mappings are in the workbook `domain-ontology/additional-info.md`.
  - `meta/state_machine/machine.als` — generic FSM framework reifying common-module's `StateEngine` (DT-003): `State`/`Signal`/`Guard`/`Transition`/`StateMachine` + once-stated well-formedness/determinism FACTS + checkable `allStatesReachable`/`liveSignals`/`firedInto`. Concrete machines extend `State`/`Signal` and pin a `StateMachine` atom.
  - `meta/scalar/scalar.als` — the foundational numeric primitive `Scalar` (an abstract decimal: `splus`/`smul`/`sneg`, `SZero`/`SOne`, and the `ringAxioms` PREMISE — not a global fact). Its own module so every quantitative layer shares one number type; concrete bounded fixed-point realization in `meta/keyed_value_algebra/scalar_int.als`. Design: `design/meta/kernel/scalar.md`; practice: `modeling/scalar-arithmetic.md`.
  - `meta/keyed_value_algebra/keyed_monoid.als` — keyed additive ℤ-module reifying common-module's `MultiMoney` (DT-005): a value is a normal-form map `key -> lone Scalar` (`add`/`scale`/`negate`/`zero`); add same-key sums, different keys widen, zero-nets collapse. Opens `meta/scalar` for `Scalar`. Instantiate `MultiMoney = Currency -> lone Scalar`, `MultiQuantity = Unit -> lone Scalar`.
  - `meta/keyed_value_algebra/keyed_order.als` — optional order/sign/equality extension (DT-005): a posited linear order on `Scalar` (`orderAxioms` premise — a true order can't be finite + ring-compatible, so it's assumed) gives the component-wise partial order `lte`, sign `classify` (ZERO/POSITIVE/NEGATIVE/INDETERMINATE), and `semanticEq` (EQUAL/UNEQUAL/UNDETERMINED). Heavily commented for teaching.
  - `meta/examples/` — **the modeling cookbook**: runnable, `make`-verified pattern recipes on a neutral Hotel domain, plus a UML/FP Rosetta table. **Learning or refreshing a pattern? Start at `meta/examples/README.md`.** Files are `exNN_*.als` (the `ex` prefix is required — module path components can't start with a digit). New `meta` machinery ships with an example here.
  - `meta/x731_state/state.als` — ITU-T X.731 expressed via `meta/state_machine`: three region machines (Operational ∥ Usage ∥ Administrative) + `Resource` host + interlocks as cross-region invariants (DT-003).
  - `meta/certainty/certainty.als` — ordered confidence levels (`LOW<MEDIUM<HIGH`) + staleness-decay rule (decay never raises certainty); DT-010. Time→step mapping pending a time-metric.
  - `meta/time/{time,duration}.als` — the time substrate (DT-001.03, DT-010): `meta/time/time` is the ordered `Instant` axis (`TimeInterval`, calendar periods `PeriodSpec`/`endOfPeriod` under the `calendarAxioms` premise, and the instant→duration metric `TimeMetric.span`/`durationBetween`); `meta/time/duration` is the standalone, totally ordered `Duration` value type, kept separate so value-object users (`meta/values`, `ItemSupply.averageLeadTime`) depend on it **without** the arity-4 metric. More time modules will land here.
  - `meta/model_time/model_time.als` — **model time** (DT-001.03): the ordinal/causal axis `Tick` (a reified total order via `util/ordering[Tick]`; causal vocabulary `precedes`/`follows`/`notAfter`). Distinct *kind* from domain time — carries no magnitude/wall-clock, only succession. NOT the Alloy 6 `var`/trace (the occurrence log must be a queryable, stampable atom set).
  - `meta/occurrence/occurrence.als` — the **two-clock bridge**: `abstract sig Occurrence { tick: one Tick, at: one Instant }` + `OneOccurrencePerTick` + the `clocksAligned` **premise** (forward-monotone; *not* assuming it = backdating). The ONLY module naming both clocks, so the two never conflate (modeling-conventions §3.3). DT-006's operation occurrences `extend Occurrence`.
  - `meta/action/{outcome,action}.als` — **Action** framework (DT-006, Layer 1): an `Action extends Occurrence` performed `by` a `Principal` (actor) over a `context` (binding footprint), bracketed by an **admission guard** (pre-projection) and a **commit guard** (post-projection), with `Decision = Accepted | Rejected{because: Reason}`; `committed`/`blockedBy` derived. **State-as-projection**: NO `World`, no domain `var` — state is a **fold over the reified, `Tick`-ordered log** (`keyed_sum[Occurrence]` for levels, LOCF for last-write-wins); a refused action contributes nothing (rollback is free). The framework is state-agnostic; the test root works an existence projection (`existsAt` over committed `Create`/`Delete`). Dynamics (duration/scheduling/serialization) deferred to Layer 2. Design: `design/meta/action/`.
  - `meta/principal/principal.als` — **Principal** (a DT-006 foundation): the responsible identity ("who") in provenance. **Fully an `Entity`** (identity `eId`, soft-ref-resolvable) with a unique readable handle `name`; **NOT `Scoped`** (global — sibling of `Scoped`, so tenant-scoping is excluded by typing). `principal` (not `agent`, reserved for the later "acting on behalf of"); `kind` (human/system) deferred.
- Domains: `system reference_data resources procurement shop_access fulfillment operations receiving shipping oam workflows_and_integrations`. Only `reference_data` (Item/ItemSupply/BusinessAffiliate/BusinessRole; Item carries the inventory-tracking `UomScheme`, DT-009 — see `reference_data/item/uom.als` + the multi-unit `collapse` in `reference_data/item/uom_collapse.als`) and `resources` (KanbanCard; InventoryItem; **InventoryPool** — a Scoped set of InventoryItems under one Item, `resources/inventory_pool/`, DT-004) have content; the rest are stubbed (`.gitkeep`).
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
- Every file declares `module <path-under-alloy>` (e.g.
  `module resources/kanban_card/kanban_card`,
  `module resources/kanban_card/tests/kanban_card`, `module meta/std/iof`).
- `open` uses paths-from-`alloy/`: `open meta/x731_state/state`,
  `open reference_data/item/item`.

## Library vs. root (where commands live)

- **Library files** (`meta/…`, `<domain>/<module>/<file>.als`) carry all
  model-defining elements: `sig`, `fact`, `fun`, and co-located checkable `assert`/`pred`.
- **Only root files carry `run`/`check`.** A root does **not** execute commands
  from the modules it opens. Roots are the `tests/*.als` files.
- Open a **root** in the GUI / pass it to `exec`; never a library module.

## Tests & command tiers

- Tests live in a **`tests/` subdirectory**: per-module suite at
  `<domain>/<module>/tests/<file>.als`; domain-level cross-module suite at
  `<domain>/tests/<domain>.als` (named after the domain — avoid the overloaded word
  "aggregate"); whole-system at `tests/system.als`. (NOT `*.test.als` — dotted module
  names are illegal.)
- **Command-name tiers** (for wildcard selection): `unit_*` (module), `dom_*`
  (domain-level), `sys_*` (system). New commands follow this; relocated
  commands kept their original names (`showSimulation`, `X731Consistency`).
- **No master root** aggregates suites — the Makefile iterates `tests/` roots.

## Running

From the repo root: `make check-alloy` (all test roots), `make check-examples` (the
cookbook), `make test-unit`, `make test-sys`, `make alloy` (GUI). Direct: `java -jar tools/alloy.jar exec -c "<name|glob|*>" -o /tmp/ao -f <root>.als`.
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

Canonical structure spec + rationale: workbook notebook `domain-ontology` (organized into
`modeling/`, `design-topics/`, `design/`) → `modeling/alloy-repository-structure.md`,
`design-topics/dt-001-alloy-directory-structure.md` (layout, DT-001.01 decided),
`design-topics/dt-002-bridging-owl-standard-models.md` (vendoring),
`modeling/modeling-conventions.md` (DAG/aggregation/refs/tight-by-default),
`design/reference-data/index.md` +
`design/resources/kanban-card/kanban-cards-entities.md` (code-authoritative entity
inventories). `meta/kernel` is implemented; the reference_data slice and the
code-faithful `KanbanCard` are modeled. Next: populate `meta/std` (DT-002), enrich
fields, and decide the event-history/bitemporal depth (DT-001.03).
