# `meta/examples` — the modeling cookbook

The **on-ramp** for designers. Each example is a small, **runnable, `make`-verified**
Alloy file that demonstrates *one* modeling pattern in the smallest form, with a fixed
recipe header. Come here to learn a pattern, copy a correct starting point, or refresh
how a tricky concept (state machines, parallel regions, bitemporality) is expressed.

Why runnable: prose rots, a green `check` cannot. The examples are simultaneously a
tutorial **and** a regression suite for the idioms. Run them with `make check-examples`.

## The shared domain — a Hotel property-management system

To avoid term-bleed with the manufacturing domain, **every example uses one neutral
cast** (learn it once):

| Term | Role | Illustrates |
|---|---|---|
| **Hotel** | the tenant boundary (one property in a multi-property PMS) | tenant / scope |
| **RoomType** | an **extensible classification** — Suite, King, Double Queen, Single, Beach View, Patio View, … (reference data; grows as *atoms*, not code) | type side of type/instance |
| **Room** | a physical room ("101"), classified by a RoomType | instance side; parallel-region state |
| **Reservation** | a booking: guest + dates + rate | aggregate root; lifecycle |
| **Guest** | the person booking | soft-reference target |
| **RatePlan** | nightly pricing, effective over date ranges | bitemporal |
| **Money / DateRange** | rate, stay window | value objects (no identity) |

`RoomType` (type) vs `Room` (instance) is the neutral stand-in for the live model's
`Item` vs `InventoryItem`; the Room's three orthogonal state regions stand in for X.731.

The cast and its relationships (preview with the VS Code PlantUML plugin):

```plantuml
@startuml
hide empty members
entity Hotel <<tenant>>
entity RoomType <<classification>>
entity Room <<instance>>
entity Reservation
entity Guest
entity RatePlan <<bitemporal>>
Hotel "1" o-- "*" Room : owns
Room ..> RoomType : classified-as
Reservation ..> Guest : guest
Reservation ..> Room : room
Reservation ..> RatePlan : rate
note bottom #white : every entity is scoped to a Hotel (tenant)
@enduml
```

## Catalog (the tour, in reading order)

| # | Pattern | Status | UML / FP analogue |
|---|---|---|---|
| 01 | Identity & the `Entity` bound | planned | UML class; identity |
| 02 | Tenant scoping + soft refs + `resolve` | **ready** | association by FK; partition |
| 03 | Aggregation (parent→child) | planned | composition/aggregation |
| 04 | Type / instance (extensible classification) | **ready** | «type»/«instance»; powertype |
| 05 | Value objects | planned | value type / no identity |
| 06 | Subtype vs. generics | planned | generalization; bounded generics |
| 07 | Enumerations (closed set) | planned | enumeration |
| 08 | State machine (reified) | planned | UML state machine |
| 09 | Parallel / orthogonal regions | **ready** | AND-states; the X.731 twin |
| 10 | Tight by default (no-orphan, forcing function) | planned | (no clean UML analogue) |
| 11 | Change & the frame problem | deferred (DT-001.03) | operation; FP `old→new` |
| 12 | Bitemporality (versions as data) | deferred (DT-001.03) | temporal/historized data |

"Ready" = a runnable file exists. "Planned" = a catalog slot to fill as the pattern is
needed. "Deferred" = waits on a modeling decision not yet made (the behavioral/temporal
layer, DT-001.03) — we do not pre-decide it here.

See also: [rosetta-uml.md](rosetta-uml.md) (the full UML/FP ↔ Alloy translation table)
and the workbook `modeling-conventions.md` (the *why* behind each convention).

## Conventions

- **One pattern per file**, named `exNN_pattern_name.als` (`module meta/examples/exNN_pattern_name`). The `ex` prefix is required — Alloy module path components cannot start with a digit.
- **Self-contained**: an example opens `meta/*` machinery but defines its own toy Hotel
  sigs — it never depends on a domain module (`reference_data`, `resources`), so it stays
  minimal and fast.
- **Fixed recipe header** (copy [`ex00_template.als`](ex00_template.als)): Pattern / UML /
  FP / Use-when / Avoid / See-also.
- **Every file is a root** carrying `run`/`check` — never `open`ed by other code.
- **Diagrams welcome.** Where a picture clarifies, embed a PlantUML diagram — in a
  fenced ` ```plantuml ` block in markdown, or inside a `/* … */` block comment in an
  `.als` file (preview with the VS Code PlantUML plugin). In `.als` comments, do **not**
  prefix the diagram lines with `*` — a leading `*` corrupts the PlantUML the plugin
  extracts; keep the `@startuml…@enduml` lines flush. Validate via the PlantUML MCP tool
  before committing (workspace convention).
- **Express invariants/constraints OCL-style: `//{ expr }//`** — braces (the UML
  constraint notation) in creole italic, attached to the constrained element(s).
  **Stay dependency-free:** do NOT use `<latex>`/`<math>` — math-to-SVG needs Apache
  Batik, which the stock local `plantuml.jar` lacks (it fails in the VS Code preview).
  Plain creole (`//italic//`, `<b></b>`, `{ }`) renders everywhere with no extra setup.
- **Render entity sigs as `entity`** (not `class`) to align with the kernel's `Entity`
  bound, and give notes a **`#white`** background (`note as N #white` / `note … #white :`)
  so they stay unobtrusive against the diagram.
- **Definition of done for new `meta` machinery: it ships with an example here.** That
  rule keeps the cookbook from going stale — framework and tutorial move together.

## Running

```bash
make check-examples                 # run every example (verified idioms)
java -jar tools/alloy.jar exec -c "*" -o /tmp/ao -f alloy/meta/examples/ex02_scoping_and_soft_refs.als
```
