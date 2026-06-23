# Manufacturing Kanban Model — `alloy/`

Alloy 6 model of the pull-based Kanban shop-floor system — the dynamic /
behavioral counterpart to the OWL ontology in `../owl/kanban.ttl`.

## How to open / run

Open **`kanban.als`** in the Alloy Analyzer (`java -jar ~/tools/alloy/alloy.jar`).
It is **self-contained** — no `open` statements, so no module-resolution issues.

- **Execute → Run showSimulation**, then **Show Latest Instance** (⌘L) and step the
  trace (Prev/Next) to watch the 8-state Kanban lifecycle and the X.731 resource
  states evolve. (A `run` that is SAT is viewable; the `check` below is not.)
- **Execute → Check X731Consistency** — verifies the state-interlock invariant
  (UNSAT = no counterexample = holds).
- **Execute → Show Metamodel** (⌘M) — static signature/field/extends diagram.

Headless: `java -jar ~/tools/alloy/alloy.jar exec -c "*" -f kanban.als`.

## Content

Stations (source / sink / processing), Resources (Equipment, Personnel, Loop),
KanbanCard, Job, InventoryLot, ItemType, the X.731 three-vector resource state
model (operational / usage / administrative) and the 8-state Kanban lifecycle.
`var` fields carry the mutable state; predicates encode the transition
operations and `fact`s the invariants.

## Relationship to the rest of the project

| | `../owl/kanban.ttl` (Protégé) | `kanban.als` (Alloy) |
|---|---|---|
| Captures | static structure + IOF/BFO alignment | behavior over time: traces, invariants |
| Lens | classification / consistency | bounded model finding / counterexamples |

The earlier placeholder scaffolding (a modular `core/material/resource/process/
quantity` mirror) is archived in `../alloy-sample/`.

---

Copyright: (c) Arda Systems 2025-2026, All rights reserved
