#!/usr/bin/env bash
# solver-progress.sh — extract plottable progress proxies from a gimsatul verbose
# log (the `-v` per-thread report lines). Companion to the CNF cache (PDEV-1711):
# cnf-export.sh produces the problem, gimsatul solves it, this reads how the solve
# is going.
#
# A CDCL solver has no sound "percent complete" — it halts on a satisfying
# assignment (SAT), on deriving the empty clause (UNSAT: a conflict at decision
# level 0), or on its budget (UNKNOWN). What CAN be watched are proxies:
#
#   variables    active variables left after in-processing — the only monotone
#                signal; shrinking = the formula is genuinely simplifying
#   level        mean decision level at conflict — for a check (UNSAT expected),
#                trending DOWN means contradictions arrive earlier: the proof is
#                tightening toward the level-0 conflict that ends it
#   trail_pct    fraction of variables assigned at conflict — the SAT-side mirror
#                (trending toward 100% suggests an assignment is reachable)
#   rate         conflicts/sec as gimsatul reports it — health, not progress:
#                flat = productively grinding, collapsing = thrashing
#   glue         learned-clause quality (lower is better)
#
# Stagnation across ALL proxies is the rational budget-termination trigger the
# DT-024 blind wall-clock cap lacks; --summary computes exactly that reading.
#
# Usage:
#   tools/solver-progress.sh <gimsatul.log> [points]   TSV to stdout (default
#                                                      ~100 rows, downsampled;
#                                                      0 = every report line)
#   tools/solver-progress.sh --summary <gimsatul.log>  human trend table + verdict
#
# Thread 0's report lines (`c0 r ...`) stand for the run: gimsatul threads share
# clauses, so their trajectories track each other closely.

set -u
die() { echo "solver-progress: $*" >&2; exit 2; }

mode=tsv
if [ "${1:-}" = "--summary" ]; then mode=summary; shift; fi
log=${1:-}; points=${2:-100}
[ -n "$log" ] || die "usage: solver-progress.sh [--summary] <gimsatul.log> [points]"
[ -f "$log" ] || die "no such log: $log"

# c0 r <seconds> <MB> <level> <reductions> <restarts> <rate> <conflicts>
#      <redundant> <trail%> <glue> <irredundant> <variables> <vars%>
extract() {
  awk '$1 == "c0" && $2 == "r" && NF >= 14 {
    gsub(/%/, "", $11)
    print $3 "\t" $9 "\t" $8 "\t" $5 "\t" $11 "\t" $12 "\t" $4 "\t" $13 "\t" $14
  }' "$log"
}

case "$mode" in
tsv)
  echo -e "seconds\tconflicts\trate\tlevel\ttrail_pct\tglue\tmb\tirredundant\tvariables"
  if [ "$points" = 0 ]; then
    extract
  else
    extract | awk -v n="$points" '
      { line[NR] = $0 }
      END {
        step = (NR > n) ? int(NR / n) : 1
        for (i = 1; i <= NR; i += step) print line[i]
        if (i - step != NR) print line[NR]   # always include the final report
      }'
  fi
  ;;
summary)
  verdict=$(grep -m1 '^s ' "$log" | cut -d' ' -f2-)
  extract | awk -v verdict="${verdict:-UNKNOWN (no s-line: budget stop or still running)}" '
    { line[NR] = $0 }
    END {
      if (NR < 3) { print "too few report lines (" NR ") — run gimsatul with -v"; exit 1 }
      split(line[1], a); split(line[int(NR * 2 / 3)], b); split(line[NR], c)
      printf "verdict: %s\n", verdict
      printf "reports: %d   span: %.0fs -> %.0fs\n\n", NR, a[1], c[1]
      printf "%-12s %12s %12s %12s   %s\n", "proxy", "first", "at-2/3", "last", "reading"
      trend("variables", a[9], b[9], c[9], "down = simplifying")
      trend("level",     a[4], b[4], c[4], "down = proof tightening (UNSAT-bound)")
      trend("trail_pct", a[5], b[5], c[5], "up = assignment reachable (SAT-bound)")
      trend("rate",      a[3], b[3], c[3], "flat = healthy, collapsing = thrashing")
      trend("glue",      a[6], b[6], c[6], "down = better learned clauses")
      # Stagnation: the two progress proxies both moved <1% over the last third.
      dv = rel(b[9], c[9]); dl = rel(b[4], c[4])
      printf "\nlast-third movement: variables %.2f%%, level %.2f%% -> %s\n",
        dv * 100, dl * 100,
        (dv < 0.01 && dl < 0.01) ? "STAGNANT (budget-terminate is rational)" \
                                 : "PROGRESSING (extending the budget buys real work)"
    }
    function trend(name, x, y, z, note) {
      printf "%-12s %12s %12s %12s   %s\n", name, x, y, z, note
    }
    function rel(x, y) { return (x == 0) ? 0 : (x > y ? x - y : y - x) / x }
  '
  ;;
esac
