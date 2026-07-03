module reference_data/item/item_implementation

/*
 * ITEM — IMPLEMENTATION (DT-017). Integration roots open this file to get the REAL module.
 *
 * DEGENERATE CASE (a DT-017 finding): item is a STATIC reference module — there is no deeper
 * machinery (no log, no derivation) from which its laws could be PROVEN, so the implementation
 * simply asserts the contract as fact, exactly as the mock does. The two files are identical
 * today and will diverge the day the module gains derived content (e.g. supply-selection
 * policy); consumers must NOT rely on the coincidence. The suite's obligation here is joint
 * SATISFIABILITY of the axioms (witnesses in tests/), not discharge proofs.
 */

open reference_data/item/item_contracts

fact ItemGuarantees { guarantees }
