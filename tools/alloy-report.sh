#!/usr/bin/env bash
# make report — render every Alloy run/check outcome with its LOGICAL reading.
#
#   ∃  satisfiable run  — a witness should exist        (expect 1)
#   ∄  negative run     — a scenario that must be forbidden (expect 0)
#   ∀  check            — an invariant / universal claim (expect 0, i.e. no counterexample)
#   ✓  the outcome matched its `expect`   ✗  MISMATCH (also flips the process exit code)
#   ·  no `expect` set on the command (label inferred from the result; not gated)
#
# The label is derived from (command kind, the command's `expect` parsed from source, the SAT/UNSAT
# result). Usage:  tools/alloy-report.sh [--examples]
set -u
JAR=tools/alloy.jar
OUT=out/alloy          # Alloy -o dir (java recreates it each run)
LOG=out/.report.log    # keep the stdout log OUTSIDE -o, or java wipes it
mkdir -p "$OUT"

if [ "${1:-}" = "--examples" ]; then
  roots=$(find alloy/meta/examples -name '*.als' ! -name 'ex00_*' | sort)
else
  roots=$(find alloy -path '*/tests/*.als' | sort)
fi

fail=0
for f in $roots; do
  echo "== $f =="
  java -jar "$JAR" exec -c "*" -o "$OUT" -f "$f" > "$LOG" 2>&1 || fail=1
  # arg1 = source (build name->expect map); arg2 = exec log (kind/name/result -> label)
  awk '
    FNR==NR {
      if ($1=="run" || $1=="check") pend=$2;               # remember the command name
      if (pend!="" && match($0, /expect[ \t]+[0-9]+/)) {   # capture expect (same line OR a later one)
        s=substr($0,RSTART,RLENGTH); gsub(/[^0-9]/,"",s); ex[pend]=s; pend=""
      }
      next
    }
    /^[ \t]*[0-9]+\.[ \t]+(run|check)[ \t]/ {
      k=$2; name=$3; res="";
      for (i=1;i<=NF;i++) if ($i=="SAT"||$i=="UNSAT") res=$i;
      e = (name in ex) ? ex[name] : -1;
      if (k=="check")      q="\342\210\200";              # universal claim
      else if (e==1)       q="\342\210\203";              # existential (positive run)
      else if (e==0)       q="\342\210\204";              # impossibility (negative run)
      else                 q=(res=="SAT")?"\342\210\203":"\342\210\204";
      if (e==-1) { mark="\302\267"; desc="(no expect set)" }
      else {
        ok = ((e==1 && res=="SAT") || (e==0 && res=="UNSAT"));
        mark = ok ? "\342\234\223" : "\342\234\227";      # check / cross
        if (q=="\342\210\203")      desc = ok ? "satisfiable -- witness exists" : "NO WITNESS -- over-constrained";
        else if (q=="\342\210\204") desc = ok ? "forbidden -- as intended"      : "LEAK -- forbidden state reachable";
        else                        desc = ok ? "holds -- no counterexample"    : "COUNTEREXAMPLE -- property false";
      }
      printf "  %s %s  %-36s %-5s  %s\n", mark, q, name, res, desc;
    }
  ' "$f" "$LOG"
done

echo
if [ "$fail" -ne 0 ]; then
  echo "MISMATCH: at least one command did not match its expect (see the cross rows above)."; exit 1
else
  echo "OK: every annotated command matched its expect."
fi
