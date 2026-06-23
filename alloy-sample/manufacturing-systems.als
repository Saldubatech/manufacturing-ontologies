module manufacturing_systems   // Alloy identifiers cannot contain '-' (file stays manufacturing-systems.als)

open modules/core/core
open modules/material/material
open modules/resource/resource
open modules/process/process
open modules/quantity/quantity

/*
 * Root model — opens every module, mirroring owl/manufacturing-systems.ttl.
 *
 * Open THIS file in the Alloy Analyzer, then pick a command from the
 * "Execute" menu. All `open` paths are resolved relative to this file's
 * directory (alloy/), which is why module names are written as paths from
 * here (e.g. modules/core/core).
 */

-- Show a small, non-trivial instance touching every module.
pred show {
  some ManufacturingProcess
  some Operation
  some PhysicalQuantity
  some Machine
  some Material
}
-- Scope must exceed the number of distinct entities `show` requires: Machine +
-- Material + Operation + ManufacturingProcess + PhysicalQuantity all share the
-- abstract Entity supertype, so a scope below 5 is unsatisfiable.
run show for 8

-- Sanity assertion: every process has at least one operation (holds by the
-- `some Operation` multiplicity in the process module; the check should find
-- no counterexample).
assert ProcessesHaveOperations {
  all p: ManufacturingProcess | some p.hasOperation
}
check ProcessesHaveOperations for 6
