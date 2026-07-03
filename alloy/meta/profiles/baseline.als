module meta/profiles/baseline

/*
 * P0 — BASELINE: the structural profile (DT-012). Identity, soft references, tenant scoping —
 * and nothing else: no time, no quantities, no premises. For reference/catalog modules (entities,
 * classifications, refs). Every domain module opens exactly one profile; this is the smallest.
 */

open meta/profiles/profile
open meta/kernel                  // Entity/Scoped, EntityId, resolve, refs, tenant isolation

/** P_Baseline — the marker: this universe models under the baseline (structural) profile. */
one sig P_Baseline extends Profile {}
