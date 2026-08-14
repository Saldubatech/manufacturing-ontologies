# InventoryItem `var`/LTL carrier — ARCHIVED (DT-011)

The original Phase-B carrier of the InventoryItem model — `var` state fields + 17 transition
predicates + three suites (`tests/{inventory_item,lifecycle,operations}.als`, 77 commands), frozen
VERBATIM at D17 — archived here 2026-07-02 when the canonical occurrence-log carrier
(`alloy/resources/inventory_item/`) reached **full parity** (44/44; parity map in the workbook
`design/resources/inventory-item/verification/occurrences.md`).

Unlike `kanban_sim/`, this archive is **not self-contained**: the files keep their original
`module resources/inventory_item/legacy/...` paths (verbatim freeze) and open the live
`alloy/{meta,shared,reference_data}` tree. To run it, either:

- check out a commit at or before `bc49c08` (where it lived under
  `alloy/resources/inventory_item/legacy/` and ran green), or
- temporarily move this directory back to `alloy/resources/inventory_item/legacy/` — the module
  paths still match that location. (It was gate-excluded and lint-isolated there; nothing in the
  live model may open it.)
