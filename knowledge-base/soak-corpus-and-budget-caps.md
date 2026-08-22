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

## The CNF artifact cache (PDEV-1609 — the model's "class files")

`make cnf-export ROOT=<root.als> COMMAND=<cmd>` translates one command to DIMACS
(`exec -s CNF`) and stores it gzipped at `cnf/<scope_hash>/<command>.cnf.gz`, indexed
in `cnf/manifest.tsv` (columns: `registered, model_sha, alloy_version, root, command,
scope_hash, vars, clauses, path`). MP direction 2026-08-21.

- **Cache, not artifact of record**: keyed by `(command, scope_hash, alloy_version)`
  — the same cone hash the soak planner uses (`tools/soak-chunk.sh conehash`), so a
  model change outside a command's cone keeps its CNF valid, and an alloy.jar bump
  invalidates everything. `model_sha` is a browsing stamp, not part of the key. A key
  hit is a no-op; `FORCE=1` re-exports. `cnf/` is gitignored, like `corpus/`.
- **Determinism stance**: Alloy's translation is not byte-stable across runs; the
  cache promises equivalence (same problem at the same scope), not identity — nobody
  diffs class files, they rebuild.
- **What a CNF buys**: the integration seam for EXTERNAL solvers (kissat, CaDiCaL,
  parallel portfolios) without touching the Alloy toolchain. For a `check`, an
  external **UNSAT verdict = the law holds at that scope** and transfers as-is. An
  external **SAT** proves a counterexample exists but does NOT reconstruct the Alloy
  witness (the variable↔atom mapping is not exported) — rerun in Alloy for the
  instance, or drop scope.
- Translation cost is minutes even for the hardest instances (the 7.2M-clause
  receiver soak translated in ~2 min); the search time is what the cache can shop
  around to better solvers.
- **Watching a solve** (`tools/solver-progress.sh <gimsatul.log>`): a CDCL solver has
  no sound percent-complete — it halts on SAT (full satisfying trail), UNSAT (the
  empty clause: a conflict at decision level 0), or its budget (UNKNOWN). The script
  extracts the plottable proxies from a gimsatul `-v` log (TSV mode) and `--summary`
  reads the trend: active **variables** shrinking = real simplification; mean
  conflict **level** falling = the UNSAT proof tightening; **rate** flat = healthy.
  Its stagnation reading (both progress proxies <1% movement over the last third)
  is the budget-termination criterion a blind wall-clock cap lacks. Calibration
  point: the 2026-08-21 gimsatul run on the receiver-soak CNF (4 threads, 6h) hit
  its wall still PROGRESSING (variables −5%, level −11% in the last third) —
  glucose's 6-day solve of the same command is formula hardness, not solver
  weakness. Second calibration point (2026-08-22, 6 threads, 10h, same CNF):
  UNKNOWN again, with the stagnation boundary now visible — active variables
  moved only 0.26% in the last third (340k residual, flatlined) while mean
  conflict level still moved 3.07% (1843 → 158 over the run); conflict rate
  decayed 184 → 12. One more equal extension would likely put both proxies
  under the 1% threshold: the rational budget-termination point. Together the
  three runs (glucose 6d+ blind; 4t/6h both proxies brisk; 6t/10h one proxy
  stalled) are the DT-024 calibration set.
