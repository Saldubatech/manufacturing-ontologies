module meta/profiles/profile

/*
 * Profile — the marker base for PRE-PACKAGED MODELING PROFILES (DT-012). A profile module bundles
 * an opt-in composition (opens + premises-as-facts + a marker): OPENING A PROFILE IS THE ACT OF
 * ADOPTING IT, and the adoption transits to every root in the cone. Markers make the adopted
 * profiles VISIBLE in every instance/evaluator session; `make profiles` prints the per-root summary.
 *
 * Profiles are ADDITIVE (opens unify; higher profiles open lower ones). Advanced/special-case
 * modeling bypasses profiles and composes from the base modules à la carte (where every premise
 * remains a plain predicate) — see the opt-in catalog, design/meta/index.md.
 */

/** Profile — a marker: one atom per adopted profile, visible in every instance. */
abstract sig Profile {}
