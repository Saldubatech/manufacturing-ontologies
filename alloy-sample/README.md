# Manufacturing Systems Model — `alloy-sample/` (ARCHIVED)

> **Archived placeholder.** This is the original scaffolding Alloy project — a
> modular `core/material/resource/process/quantity` mirror of the early OWL
> placeholders, retained as a worked example of multi-file Alloy module structure
> (`open` + per-module layout). It is **not** the live model. The live Kanban
> model is `../alloy/kanban.als`.

Modular formal model of manufacturing systems in the **Alloy** modelling
language, analysed with the **Alloy Analyzer**. Sibling to `owl/`: same domain,
same module decomposition, different formalism (relational first-order logic +
bounded model finding, rather than OWL/Description-Logic + reasoning).

## How to open

Open **`manufacturing-systems.als`** in the Alloy Analyzer
(<https://alloytools.org>), then choose a command from the **Execute** menu:

- `run show for 8` — find a small instance touching every module (Analyzer
  shows it in the visualizer). The scope must exceed 5: the five "some …"
  signatures share the abstract `Entity` supertype, so smaller scopes are
  unsatisfiable.
- `check ProcessesHaveOperations for 6` — look for a counterexample to the
  sample assertion (none expected → reported UNSAT).

### Command-line (headless)

The Alloy Analyzer also runs without the GUI, which is how this model was
validated:

```bash
java -jar /path/to/alloy.jar exec -c "*" -f manufacturing-systems.als
# add `-D info` to see SAT/UNSAT per command
```

## Layout

```
alloy/
├── manufacturing-systems.als     # ROOT — opens all modules; open this
└── modules/
    ├── core/core.als             # abstract sig Entity + relatesTo
    ├── material/material.als      # opens core
    ├── resource/resource.als      # opens core
    ├── process/process.als        # opens core + material + resource
    └── quantity/quantity.als      # opens core; abstract Unit / QuantityKind
```

## Module system & path resolution

- Each file declares `module <path>` where `<path>` is its location **relative
  to `alloy/`** (e.g. `module modules/core/core`).
- Imports use `open <path>` with that same path-from-`alloy/` form.
- The Alloy Analyzer resolves every `open` relative to the directory of the
  **root file you loaded**. So load `manufacturing-systems.als` (whose directory
  is `alloy/`) and all paths resolve. Loading a sub-module file directly changes
  the base directory and breaks the `open` paths — open the root.

## Dependency graph

```
   material   resource   quantity        process
        \        |          |            /  |  \
         \       |          |  (core) ←─┘   |   └→ (material, resource)
          └──────┴────→ core ←─────────────┘
```

`process` opens `core` + `material` + `resource` because its relations
(`usesResource`, `consumesMaterial`, `producesMaterial`) target those modules'
signatures. The root opens all five.

## Correspondence to `owl/`

| Concept | `owl/` (OWL/Turtle) | `alloy/` (Alloy) |
|---|---|---|
| Top type | `core:Entity` ⊑ `bfo:entity` | `abstract sig Entity` |
| Generic association | `core:relatesTo` (object property) | `relatesTo: set Entity` field |
| Subtype | `rdfs:subClassOf` | `extends` |
| Cross-module relation | object property w/ range in another module | field whose type is in an `open`ed module |
| Units | external **QUDT** import | abstract `Unit` / `QuantityKind` (no external import) |
| Tooling | Protégé + ELK/HermiT reasoner | Alloy Analyzer (SAT-based model finder) |

The key modelling difference: OWL reasons over an **open world** with no fixed
bounds; Alloy searches for instances/counterexamples within a **finite scope**
(`for N`). They answer different questions — use both as complementary lenses.

## Adding a module

1. Create `modules/<name>/<name>.als` starting with `module modules/<name>/<name>`.
2. Add `open` lines for the modules it depends on.
3. Add an `open modules/<name>/<name>` to `manufacturing-systems.als`.

---

Copyright: (c) Arda Systems 2025-2026, All rights reserved
