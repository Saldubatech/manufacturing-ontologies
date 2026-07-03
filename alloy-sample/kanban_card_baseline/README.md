# KanbanCard baseline spike — ARCHIVED (DT-015 Phase B, 2026-07-02)

The original code-faithful single-entity KanbanCard model (DT-001.08 / KC-MH-9), preserved when
the split KanbanCard/CardCycle model replaced it, and ARCHIVED out of the gate when the cycle
lifecycle moved onto the occurrence log (DT-015) — the same policy as `inventory_item_legacy/`.

Not self-contained: files keep their original `resources/kanban_card/baseline/...` module paths
(verbatim freeze) and open the live `alloy/{meta,shared,reference_data}` tree. To run: check out a
commit at or before the archive, or move this directory back under `alloy/resources/kanban_card/baseline/`.
