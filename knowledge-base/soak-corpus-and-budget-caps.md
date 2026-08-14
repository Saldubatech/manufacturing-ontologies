# Soak corpus & budget caps (PDEV-1610, DT-025 phase 0)

The chunked soak runner (`tools/soak-chunk.sh`, DT-024 §6) is hardened so a night batch
leaves **durable products**, never only a verdict. Three mechanisms, all live as of
2026-08-14:

## The bulk instance corpus

Every done-SAT command's `-o` dumps are registered into `corpus/manifest.tsv` at
command completion (the launch wrapper calls `harvest-one`); `make soak-harvest
[BATCH=soak/<tag>]` back-fills batches that predate the hook. Conventions:

- **Dumps stay in place** in their batch dir (`soak/<tag>/cmd/<command>.d/`); the
  manifest is the index, not a copy store. Batch dirs are immutable history — never
  clean them while the manifest references them.
- **Manifest columns**: `registered` (epoch), `model_sha` (from `batch.meta`, stamped
  at plan time; `+retro` suffix when back-filled without one), `root`, `command`,
  `scope_hash` (the command's cone hash), `batch`, `solution` (path, the dedup key).
- **Staleness** is detected by key, not by deletion: an instance is valid only for its
  `model_sha`; consumers filter on it. `scope_hash` identifies the exact cone the
  instance satisfied.
- `corpus/` is **gitignored** (regenerable machine product). The CURATED seed corpus —
  canonicalized instances that become test fixtures — is a separate, committed,
  reviewed artifact (PDEV-1613); do not point tests at the bulk corpus.
- Only `run` witnesses produce instances. `check` commands yield verdicts (their
  instance would be a counterexample — a bug find); do not expect corpus rows from
  them.

## Budget-cap watchdog

Orthogonal to LENIENT (which governs only WINDOW-end behavior, per MP 2026-08-11): the
dispatcher kills any running command past its cap and records
`cmd/<command>.overbudget`; `soak-status` reports it as `OVER-BUDGET`, distinct from
`ERROR`.

- Cap = `estimate × CAP_NUM` (default 3) when the scope-hash-matched estimate exists;
  `UNKNOWN_CAP` (default 21600 s = 6 h) otherwise. `CAP_NUM=0` / `UNKNOWN_CAP=0`
  disables.
- An OVER-BUDGET row is a **frontier bracket point** — "too hard at this scope" — the
  raw material for the DT-025 R2 bisection planner (PDEV-1616), and a candidate for
  the FULL profile. It is NOT a failure and NOT wasted compute.
- The kill targets the JVM (the `sh` wrapper's child), so the wrapper still writes
  `rc`, the end epoch, and runs the harvest hook. Killing the wrapper pid by hand
  orphans the JVM — use the watchdog, or `pkill -f` on the command pattern.

## Quiet window

`chunk` refuses to start while a foreign Alloy solver runs on the host (detected via
`ps` for `alloy.jar` outside the batch dir): co-running poisons both wall-clocks AND
the estimates later harvested from the ledger. `FORCE=1` overrides; dispatching while
a foreign solver appears mid-batch logs a `QUIET-WARN` instead of blocking.

## Provenance stamp

`plan` writes `batch.meta`: `created` epoch, `model_sha` (`git rev-parse HEAD`), and a
`dirty` flag. Launch batches from a **clean, pushed tree** — a dirty stamp makes every
harvested instance unreproducible.
