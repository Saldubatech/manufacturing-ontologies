# Rosetta — UML / FP ↔ Alloy ↔ our conventions

A translation table for designers who think in UML or functional types. It maps the
construct you know to the Alloy idiom, the **convention we adopted** (which is often
narrower than what Alloy allows), and the runnable example. The conventions' *rationale*
lives in the workbook `modeling-conventions.md`; this is the quick lookup.

| UML / FP | Alloy idiom | Our convention | Example |
|---|---|---|---|
| Class (with identity) | `sig` | `extends Entity` / `Scoped`; `eId` is the key | 01 |
| Attribute | field `: one T` | — | 01 |
| Multiplicity `0..1 / 1 / * / 1..*` | `lone / one / set / some` | — | 01 |
| Association / role | a relation field | **soft ref** (`EntityId`) across modules; follow with `resolve` | 02 |
| Multi-tenant partition | (none built-in) | `Scoped.tenantId`; isolation stated once in `meta/kernel` | 02 |
| Aggregation / composition | `set` field on the parent | **forward parent→child only**, no back-reference | 03 |
| «type» / «instance», powertype | two sigs + a ref | extensible classification (reference data) ← instance; **not** an enum | 04 |
| Value type (no identity) | a plain `sig`, no `eId` | lives in `meta/values`; reused, frame-free | 05 |
| Generalization / inheritance | `abstract sig` + `extends` | subtype polymorphism **replaces** generics | 06 |
| Bounded generic `T <: Bound` | parameterized module `m[T]` | avoided; use the abstract supertype + `extends` | 06 |
| Enumeration (closed) | `enum` (or `abstract sig`+`one sig`) | closed, code-level set; long form when it must `extend State`/`Signal` | 07 |
| State machine | — | reified `StateMachine` in `meta/state_machine` | 08 |
| Guard / transition condition | — | `Guard` discriminator; determinism-modulo-guard | 08 |
| Orthogonal regions (AND-states) | several state fields | one machine per region + cross-region interlock fact | 09 |
| Operation (state change Δ) | predicate `pre→post`, `'` (prime) | frame helper / relational override `++` | 11 (deferred) |
| Historized / temporal data | `Version` data + as-of fun | append-only; the Alloy trace ≠ either time axis | 12 (deferred) |

## Things with no clean UML/FP analogue (so they need their own examples)

- **Tight by default (§6)** — no-orphan facts + the "constrain until UNSAT forces an
  explicit relaxation" discipline. There is no UML notation for "the model should make
  nonsense unsatisfiable." → example 10.
- **Stated-once generic rules** — e.g. cross-tenant isolation quantified over *every*
  `Scoped` entity's `refs`, rather than drawn on each association. Alloy's quantification
  over a reified `refs` set has no diagram equivalent. → example 02.

## Where Alloy is narrower or wider than UML

- **Wider**: Alloy relations are n-ary and first-class; an "association class" is just a
  `sig`, and a ternary association needs no reification ceremony.
- **Narrower (by our convention, not the tool)**: we forbid child→parent back-references
  (DAG discipline), and we keep cross-module links *soft* (ids), where UML would draw a
  plain navigable association. The tool would allow the hard relation; we don't.
- **Different axis**: UML state machines bundle behavior (actions/effects) with structure;
  our reified machine models the *structure* (legal edges) atemporally, and defers
  behavior/effects to the temporal layer (DT-001.03).
