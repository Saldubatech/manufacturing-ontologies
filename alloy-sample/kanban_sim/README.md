# `kanban_sim` — archived Kanban behavioral spike

This is the **throwaway behavioral spike** that originally lived under
`alloy/resources/`, archived here when the real, code-faithful `KanbanCard` was
introduced into the live model (DT-001.08 redesign).

It is preserved as a **reference demonstration** of the ITU-T X.731 `var`/trace
machinery (`meta/x731_state`): a multi-station Kanban loop with a fault-interlock
simulation (`tests/kanban.als` → `run showSimulation`). It is NOT code-faithful —
its entities (`Loop`, `Station`, `Operator`, `Job`, `InventoryLot`, `ItemType`,
and the 8-stage `KanbanLifecycleState`) were invented for the spike and do not
correspond to the `operations` backend.

## Differences from the live model

- Self-contained: it carries its own copy of the X.731 state model
  (`x731_state.als`, copied from `alloy/meta/x731_state/state.als`) and is rooted
  at `alloy-sample/` (`module kanban_sim/...`), so it does not depend on `alloy/`.
- Not run by `make check-alloy` (which only globs `alloy/**/tests/*.als`).
- Run it manually:
  `java -jar tools/alloy.jar exec -c "*" -o /tmp/ao -f alloy-sample/kanban_sim/tests/kanban.als`

The live, code-faithful Kanban model lives in `alloy/resources/kanban_card.als`.
