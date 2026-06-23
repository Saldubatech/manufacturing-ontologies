module meta/tests/kernel

open meta/kernel

// The eId key constraint holds (sanity regression guard for EntityIdIsKey).
assert unit_kernel_eIdIsKey { all disj a, b: Entity | a.eId != b.eId }
check unit_kernel_eIdIsKey for 6

// The kernel loads / is not over-constrained.
run unit_kernel_loads {} for 3
