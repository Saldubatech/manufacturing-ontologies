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
- **Two non-domain layers (DT-001.12):** `meta/` (the model of the model — "how do we model?") and
  `shared/` (domain-neutral vocabulary — "what do all domains speak?"). **Layer law (lint-enforced,
  `make check-layering`, part of `check-alloy`):** `meta` never opens `shared`; `shared` opens `meta`
  freely and never a domain; domains open both. Discriminator: generic/parameterized machinery = `meta`;
  an *instantiation* with concrete vocabulary = `shared` (or the domain, when the vocabulary is
  domain-owned — cf. `uom_collapse`). `shared/` is a **per-level pattern**: any directory level may carry
  a `shared/` subdirectory for elements reused across that level's members (e.g. `reference_data/shared/`),
  with a promotion path upward as usefulness widens.
- **START HERE — `meta/profiles/` (DT-012):** pre-packaged modeling profiles adopted as a unit: `baseline` (P0 — kernel only), **`domain_log` (P1 — THE DEFAULT: stateful log anatomy + `groupAxioms ∧ orderAxioms` as FACTS)**, `timed_log` (P2 — + `Timed`/instant axis). **Opening a profile IS the opt-in** — premises transit to every root in the cone; every domain module opens exactly one profile; markers (`P_*` atoms) show adoption in instances; `make profiles` prints the per-root map. À la carte composition from the base modules is the advanced path (the opt-in catalog: workbook design/meta/index.md).
- **`meta/` is not a domain — it is a PRODUCT for domain modelers (DT-013).** Sophistication inside
  (algebras, time logics) is fine; the exported surface must be a well-defined, ready-to-use
  abstraction. Every new/changed capability ships with: an **abstraction sentence** (one header line,
  modeler vocabulary, no internal terms), task-shaped export names + named premises with a one-line
  "assume when…", a cookbook example + kit/profile integration, and its suite + catalog. A domain
  concept expressible only via the internals is a kit defect — open a DT (the ex18 test). Canonical
  statement: workbook `modeling/meta-design-contract.md`. It holds modeling machinery:
  - `meta/kernel.als` — identity + the `Entity`/`Scoped` bound, `EntityId`, soft-ref `resolve`, cross-tenant isolation (DT-001.02, implemented).
  - `meta/state_machine/machine.als` — generic FSM framework reifying common-module's `StateEngine` (DT-003): `State`/`Signal`/`Guard`/`Transition`/`StateMachine` + once-stated well-formedness/determinism FACTS + checkable `allStatesReachable`/`liveSignals`/`firedInto`. Concrete machines extend `State`/`Signal` and pin a `StateMachine` atom.
  - `meta/scalar/scalar.als` — the foundational numeric primitive `Scalar` (an abstract decimal: `splus`/`smul`/`sneg`, `SZero`/`SOne`, and the `ringAxioms` PREMISE — not a global fact). Its own module so every quantitative layer shares one number type; concrete bounded fixed-point realization in `meta/keyed_value_algebra/scalar_int.als`. Design: `design/meta/kernel/scalar.md`; practice: `modeling/scalar-arithmetic.md`.
  - `meta/keyed_value_algebra/keyed_monoid.als` — keyed additive ℤ-module reifying common-module's `MultiMoney` (DT-005): a value is a normal-form map `key -> lone Scalar` (`add`/`scale`/`negate`/`zero`); add same-key sums, different keys widen, zero-nets collapse. Opens `meta/scalar` for `Scalar`. Instantiate `MultiMoney = Currency -> lone Scalar`, `MultiQuantity = Unit -> lone Scalar`.
  - `meta/keyed_value_algebra/keyed_order.als` — optional order/sign/equality extension (DT-005): a posited linear order on `Scalar` (`orderAxioms` premise — a true order can't be finite + ring-compatible, so it's assumed) gives the component-wise partial order `lte`, sign `classify` (ZERO/POSITIVE/NEGATIVE/INDETERMINATE), and `semanticEq` (EQUAL/UNEQUAL/UNDETERMINED). Heavily commented for teaching.
  - `meta/examples/` — **the modeling cookbook**: runnable, `make`-verified pattern recipes on a neutral Hotel domain, plus a UML/FP Rosetta table. **Learning or refreshing a pattern? Start at `meta/examples/README.md`.** Files are `exNN_*.als` (the `ex` prefix is required — module path components can't start with a digit). New `meta` machinery ships with an example here.
  - `meta/time/{instant,time,duration}.als` — the time substrate (DT-001.03, DT-010), split by DEPENDENCY COST: `instant` is the **bare axis** (`Instant` + total order + `atOrBefore`/`earlierThan`/`earliest`/`latest` + `TimeInterval`/`within`) — what `meta/occurrence` (and hence the whole action/log cone) opens, split out 2026-07-02 because the metric below is ARITY-4 and **Kodkod cannot represent arity 4 once the universe exceeds ~215 atoms** (domain log universes routinely do); `time` opens instant and adds the ABSTRACT period machinery (`PeriodSpec{closes}`/`endOfPeriod`/`samePeriod` under the `calendarAxioms` premise — the real-world binding `PeriodUnit`/`TimeZone`/`CalendarSpec` is `shared/time/calendar`, DT-001.12 earmark fulfilled) and the instant→duration metric (`TimeMetric.span`/`durationBetween` under `durationAxioms`); `duration` is the standalone, totally ordered `Duration` value type, kept separate so value-object users (`shared/values`, `ItemSupply.averageLeadTime`) depend on neither the calendar nor the metric.
  - `meta/model_time/model_time.als` — **model time** (DT-001.03): the ordinal/causal axis `Tick` (a reified total order via `util/ordering[Tick]`; causal vocabulary `precedes`/`follows`/`notAfter`). Distinct *kind* from domain time — carries no magnitude/wall-clock, only succession. NOT the Alloy 6 `var`/trace (the occurrence log must be a queryable, stampable atom set).
  - `meta/occurrence/occurrence.als` — the **two-clock bridge**: `abstract sig Occurrence { tick: one Tick }` + `OneOccurrencePerTick` — MINIMAL (DT-011): the domain-time stamp is the OPT-IN subset extension `meta/occurrence/timed.als` (`Timed in Occurrence { at: one Instant }` + the `clocksAligned` **premise**; forward-monotone; *not* assuming it = backdating) — the only module naming both clocks (modeling-conventions §3.3). DT-006's operation occurrences `extend Occurrence` and opt kinds into `Timed` where wall-clock reads matter.
  - `meta/action/{outcome,action}.als` — **Action** framework (DT-006, Layer 1): an `Action extends Occurrence` performed `by` a `Principal` (actor) with **`bindings: set univ`** — its **binding environment**, the quantifier prefix of the guarded formula ("∃ x such that guard(x) then effect(x)"; a binding may be an Entity, a Value, or any model element; derived per kind from named, TYPED binding fields — decision 2026-07-01, `sig Instance` deleted) — bracketed by an **admission guard** (pre-projection) and a **commit guard** (post-projection), with `Decision = Accepted | Rejected{because: Reason}`; the three outcomes are named preds that PARTITION Action (`committed`/`refusedAtAdmission`/`refusedAtCommit`; `refusalReasons` collects a refusal's why). Guards are made evaluable per kind by the **witnessing pattern** (`admission = Accepted iff <pred>`). **State-as-projection**: NO `World`, no domain `var` — state is a **fold over the committed log prefixes** (`committedBefore[t]` = the strict PRE-projection guards read; `committedUpTo[t]` = the inclusive POST-projection; then `keyed_sum[Occurrence]` for levels / LOCF for last-write-wins); a refused action contributes nothing (rollback is free). The core is state-agnostic; cookbook `ex15` chains guarded actions and queries the projected state. Dynamics (duration/scheduling/serialization) deferred to Layer 2. Design: `design/meta/action/`.
  - `meta/action/stateful.als` — the OPTIONAL snapshot-carrying extension (DT-006 build prep): opaque `Snapshot` (domains extend it with their state record, e.g. the coming `InventoryItemState`; doubles as the future bitemporal version payload) + `StatefulAction { pre, post: lone Snapshot }` + `PostOnlyIfCommitted`. The Effect's visible seat: admission reads `pre` → the kind's value-parameterized transition core constrains `(pre, post)` (Effect witnessing) → commit reads `post`; guard reads are field access, state-at-t is LOCF of records. NAMING: `pre`/`post` — `before`/`after` are Alloy 6 temporal KEYWORDS. Domain chaining is a domain fact and must be UNCONDITIONAL (refused actions still read the real state). Cookbook: `ex17` (folio snapshot chains), `ex18` (the ex16 stack on the full machinery — the InventoryItem-build template).
  - `meta/action/attributed.als` — the OPT-IN actor stamp (DT-011): `Attributed in Action { by: one Principal }` (SUBSET sig — independent opt-ins compose under single inheritance). Without it the kernel/Principal family stays OUT of the action cone; open it for provenance/ABAC (the deferred WriteOff-authorization hook). Kinds opt in with one fact.
  - **Domain modeling? Start at the workbook `modeling/domain-log-kit.md`** — the single entry path (five idioms + extensions + the quantitative bundle); `modeling/solver-limits.md` for the tool folklore (arity-4 ceiling, scopes, JVM hygiene).
  - `meta/principal/principal.als` — **Principal** (a DT-006 foundation): the responsible identity ("who") in provenance. **Fully an `Entity`** (identity `eId`, soft-ref-resolvable) with a unique readable handle `name`; **NOT `Scoped`** (global — sibling of `Scoped`, so tenant-scoping is excluded by typing). `principal` (not `agent`, reserved for the later "acting on behalf of"); `kind` (human/system) deferred. Kept in `meta` (not `shared`): it is a structural part of the action anatomy (`Action.by`), and `meta` may not open `shared`.
- **`shared/` — domain-neutral vocabulary** (concrete signatures + instantiations of `meta` machinery; opens `meta` freely, never a domain — DT-001.12):
  - `shared/values.als` — value objects: `Money` (Currency-keyed) and `Quantity` (Unit-keyed) are **instances of the keyed monoid** (`byCurrency`/`byUnit` normal-form maps, DT-005); `PhysicalLocator` (9-level); `Label`. (`Duration` — the ordered elapsed-time value type — stays in `meta/time/duration`; the instant→duration metric in `meta/time`.)
  - `shared/measurement/quantity.als` — the **V = Quantity instantiation** of `meta/measurement[V]` (keyed MIN/MAX + `sumIn` via `keyed_sum[Measurement]`, `metricResult` dispatch; DT-008). Lives here, not in `meta`, by the instantiation rule.
  - `shared/certainty/certainty.als` — ordered confidence levels (`LOW<MEDIUM<HIGH`) + staleness-decay rule (decay never raises certainty); DT-010. Time→step mapping pending a time-metric.
  - `shared/x731_state/state.als` — ITU-T X.731 expressed via `meta/state_machine`: three region machines (Operational ∥ Usage ∥ Administrative) + `Resource` host + interlocks as cross-region invariants (DT-003).
  - `shared/std/{bfo,iof,qudt,owl_time}.als` — **boundary stubs** MIREOT'd from the public standards (only terms our entities touch, each with its source IRI). Currently STUBS; DT-002. The standards (BFO/IOF/QUDT) stay source-of-truth as a **read-only reference cache** under `../owl/imports/` (consult via ROBOT) — we no longer maintain an authored OWL ontology; harvested mappings are in the workbook `domain-ontology/additional-info.md`.
  - `shared/time/calendar.als` — CALENDARING (the DT-001.12 earmark, fulfilled): `PeriodUnit` (HOUR/DAY/WEEK), `TimeZone`, `CalendarSpec extends PeriodSpec` binding the abstract meta period machinery to the real world; future `endOfDay`/standard durations/tenant TZs land here.
- Domains: `system reference_data resources procurement shop_access fulfillment operations receiving shipping oam workflows_and_integrations`. Only `reference_data` (Item/ItemSupply/BusinessAffiliate/BusinessRole; Item carries the inventory-tracking `UomScheme`, DT-009 — see `reference_data/item/uom.als` + the multi-unit `collapse` in `reference_data/item/uom_collapse.als`) and `resources` (KanbanCard — the card is the static container + print machine; the CardCycle lifecycle is LOG-CARRIED (DT-015: `cycle_state.als` + `cycle_occurrences.als`, forward-skip guards over the reified `LifecycleConfig`, closure by withdraw/rollover; the op machine + `executionStatus` + `lastEvent` retired; the baseline spike archived to `../alloy-sample/kanban_card_baseline/`); InventoryItem — the CANONICAL log-carried module (DT-011): identity-only entity + `item_state.als` (the InventoryItemState record) + `transitions.als` (value-parameterized cores) + `occurrences.als` (fifteen StatefulAction kinds, reason-precise witnessing, stateAt/liveAt projections); the frozen var carrier was archived VERBATIM to `../alloy-sample/inventory_item_legacy/` at full parity (2026-07-02; see its README to run it); **InventoryPool** — a Scoped set of InventoryItems under one Item, `resources/inventory_item/inventory_pool.als` (part of the inventory_item module — closely coupled, they evolve together; its `var` membership stays out of the static log cone: only its own root and `tests/system.als` open it), DT-004) have content, plus `metrics.als` in the same module (the DT-007 inventory-count read side — metrics live NEXT TO the entities they measure; `operations/` is reserved for actual manufacturing/logistics operations like assembly or put-away); the rest are stubbed (`.gitkeep`).
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
- **Co-change rule (STRICT).** Every model change ships with the required verification
  changes **in the same change set**: commands/`expect`s added or updated in the affected
  roots, and the root's catalog doc in the workbook (`design/**/verification*`) trued. A
  model edit that changes verified behavior without touching its suites and catalogs is
  an **incomplete change** — new modules get a suite + catalog before they land.

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
