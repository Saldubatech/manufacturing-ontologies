# Every command carries `expect`; a plain pipe silently masks the failure

Every `run`/`check` command in every test root carries `expect 1` (SAT — the instance
must exist) or `expect 0` (UNSAT — the assertion must hold / the guard must refuse). A
result that does not match its `expect` makes the Alloy CLI exit non-zero — that exit
code **is** the test verdict.

## The trap

Piping the CLI's output straight into `grep` (to filter the noisy solver log) replaces
the CLI's exit code with grep's — a mismatch silently reads as green. The Makefile
recipes therefore capture the per-root exit code first and grep the saved log after;
any hand-rolled invocation must do the same:

```sh
java -jar tools/alloy.jar -D info exec -s glucose -c "*" -o out/alloy -f "$root" \
  > out/.run.log 2>&1 || fail=1          # capture the verdict FIRST
grep -iE 'SAT|UNSAT|error|against expectation' out/.run.log \
  | grep -ivE 'symmetr|kodkod|cnf|translat|solving'   # then filter for reading
```

## Reading a failure

- The needle is the phrase **`against expectation`** in the log — that line names the
  command whose verdict flipped.
- A guard-rejection scenario that silently becomes SAT, or a `check` that develops a
  counterexample, both surface only through this mechanism — there is no other signal.
- `make report` prints each command's **logical** outcome (exists / forall / forbidden,
  ok / mismatch) when you want semantics instead of raw SAT/UNSAT.

## Related conventions

- Command names are tiered for wildcard selection: `unit_*`, `dom_*`, `sys_*`
  (`alloy/CLAUDE.md` § Tests & command tiers).
- Solution dumps and receipts land under `out/` — gitignored, never committed.
