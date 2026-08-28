#!/usr/bin/env bash
# merge-plan.sh — deterministic re-verification plan for a set of changed .als files
# (the model-merge gate's matrix, MP-5 protocol 2026-08-28). Prints what a merge invalidates;
# runs nothing. Pair with `make merge-verify` to execute the base tier.
#
#   tools/merge-plan.sh RANGE=<a>..<b>      changed files from a commit range
#   tools/merge-plan.sh FILES="<f1> <f2>"   explicit list
#   (no args: working tree vs HEAD, like check-affected)
#
# Output sections: CHANGED · TIER (module | library | rung | soak | tooling | none) ·
# UNIT ROOTS to re-run (cone hit) · E7 RUNGS whose cone is hit (base obligations now, gates in
# the next window) · SOAK ROWS whose cone is hit (next window) · MINIMUM RE-RUN (make target).
set -eu
cd "$(dirname "$0")/.."
RANGE=""; FILES=""
for a in "$@"; do case "$a" in RANGE=*) RANGE="${a#RANGE=}";; FILES=*) FILES="${a#FILES=}";; esac; done
if [ -n "$RANGE" ]; then FILES="$(git diff --name-only "$RANGE" -- alloy tools Makefile | sort -u)"
elif [ -z "$FILES" ]; then FILES="$( (git diff --name-only HEAD -- alloy tools Makefile; git diff --cached --name-only -- alloy tools Makefile) | sort -u)"; fi
[ -n "$FILES" ] || { echo "merge-plan: no changed files"; exit 0; }
echo "CHANGED:"; for f in $FILES; do echo "  $f"; done
tier=none; lib=0; rung=0; soak=0; tool=0; mod=0
for f in $FILES; do case "$f" in
  alloy/meta/*|alloy/shared/*|alloy/conventions/*) lib=1;;
  alloy/soak/sliced/*_inductive.als) rung=1;;
  alloy/soak/*) soak=1;;
  tools/*|Makefile) tool=1;;
  alloy/*.als) mod=1;;
esac; done
# a module file opened by >= 2 other modules counts as a library change too
for f in $FILES; do case "$f" in alloy/*.als)
  stem="${f#alloy/}"; stem="${stem%.als}"
  n=$(grep -rlE "^open $stem(\[|$)" alloy --include=*.als 2>/dev/null | grep -v "/tests/" | grep -v "^alloy/soak/" | cut -d/ -f2-3 | sort -u | wc -l | tr -d ' ')
  [ "$n" -ge 2 ] && { echo "  (opened by $n modules → library) $f"; lib=1; };;
esac; done
[ $mod -eq 1 ] && tier=module; [ $rung -eq 1 ] && tier=rung; [ $soak -eq 1 ] && [ $tier = none ] && tier=soak
[ $lib -eq 1 ] && tier=library; [ $tool -eq 1 ] && tier=tooling
echo "TIER: $tier"
hits() { # pattern-list-of-roots -> roots whose cone contains any changed file
  for r in "$@"; do cone="$(tools/cone.sh "$r" 2>/dev/null || true)"; for c in $FILES; do case "$cone" in *"$c"*) echo "  $r"; break;; esac; done; done; }
echo "UNIT ROOTS (cone hit):"; hits $(find alloy -path '*/tests/*.als' ! -path '*/legacy/*' ! -path 'alloy/soak/*' | sort)
echo "E7 RUNGS (cone hit → base obligations now; _w/_s gates next window):"; hits $(ls alloy/soak/sliced/*_inductive.als 2>/dev/null)
echo "SOAK ROWS (cone hit → next window):"; hits $(ls alloy/soak/sliced/*_soak.als 2>/dev/null)
case $tier in
  library) echo "MINIMUM RE-RUN: make check   (full gate: every unit root) + every E7 rung base set";;
  tooling) echo "MINIMUM RE-RUN: make check-layering + one root per tier; full gate if what runs changed";;
  module)  echo "MINIMUM RE-RUN: make check-affected FILES=\"$(echo $FILES)\"  + the rungs listed";;
  rung)    echo "MINIMUM RE-RUN: the rung's four obligations + vacuity guards at base scope; catalogs trued (co-change)";;
  soak)    echo "MINIMUM RE-RUN: parse check only (soak tier never on the push path)";;
  *)       echo "MINIMUM RE-RUN: nothing";;
esac
