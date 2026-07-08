# conventions/ — canonical convention exemplars

Each subdirectory is a SELF-CONTAINED mini-model (MP, 2026-07-08) demonstrating ONE adopted
modeling convention in its smallest non-vacuous form, with a `tests/` root that keeps it
green in the gate forever.

Rules (lint-enforced in `make check-layering`):

- An exemplar may open `meta/`, `shared/`, and its own files ONLY.
- Nothing outside `conventions/` may open an exemplar — these are EXEMPLARS, not libraries.
  Core modules copy the shape, never the file.
- Model ids are snake_case (Alloy ids cannot carry `-`); each exemplar's design doc lives at
  `workbooks … design/conventions/<kebab-name>/index.md` (the didactic walkthrough + the
  how-to-apply-in-core mapping; the `modeling/*.md` notes remain the RULING records).
- Exemplars stay TINY: single model file where possible (the four-file split is deliberately
  elided unless the convention IS the module architecture), small scopes, fast commands.

Initial set (MP, 2026-07-08): pinning_freezing · call_first_saga · notification_convergence ·
denormalized_observables · reason_precise_refusals · metrics.
