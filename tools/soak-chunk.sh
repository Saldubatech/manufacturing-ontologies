#!/usr/bin/env bash
# soak-chunk.sh — the DT-024 §6 chunked soak runner: command-granular queue + per-batch
# ledger + resume. SAT solving is not checkpointable, so the chunk unit is the COMMAND
# and the scheduler's job is to never dispatch one it cannot afford to finish.
#
# Subcommands (driven by the Makefile targets soak-plan / soak-chunk / soak-status):
#   plan   <batch-dir>                       enumerate (root, command) pairs into plan.tsv
#   chunk  <batch-dir> <window-s> <par> <lenient>   dispatch loop (the night window)
#   status <batch-dir>                       fold artifacts into ledger.tsv + a summary
#
# Batch dir layout (soak/<YYYYMMDD-HHMM>/ at the repo root, gitignored):
#   plan.tsv            tier  root  command  scope_hash  estimate_s   (dispatch order)
#   dispatch.log        the dispatcher's decisions (dispatched / deferred / window end)
#   cmd/<name>.log      solver output          cmd/<name>.rc    exit code
#   cmd/<name>.meta     start/end epochs       cmd/<name>.d/    harvested instances (-o)
#   ledger.tsv          materialized by `status` from plan + artifacts
#
# Estimates: alloy/soak/estimates.tsv (committed) — command<TAB>scope_hash<TAB>seconds.
# An estimate counts ONLY if its scope_hash still matches (a model change under the
# command invalidates the measurement); otherwise the command is UNKNOWN and dispatches
# only while remaining window > UNKNOWN_FLOOR. Harvest new measurements from ledger.tsv.
#
# Lenient mode (MP, 2026-08-11): runs are never interrupted on going over estimate or
# window — over-runners are SURFACED at window end for a human kill/extend decision.
# (Non-lenient differs only in exit code today: it exits 1 if runs outlive the window,
# so a wrapping scheduler can react. This runner never kills a solver either way.)
set -u

ALLOY_JAR=${ALLOY_JAR:-tools/alloy.jar}
ALLOY_FLAGS=${ALLOY_FLAGS:--s glucose}
MARGIN_NUM=${MARGIN_NUM:-2}          # dispatch iff estimate * MARGIN <= remaining
UNKNOWN_FLOOR=${UNKNOWN_FLOOR:-14400} # unknown estimate: dispatch only if remaining > 4h
POLL=${POLL:-60}                      # dispatcher poll interval, seconds

die() { echo "soak-chunk: $*" >&2; exit 2; }

# ── the cone hash: root file + its transitive `open` closure (matches `make profiles`) ──
cone_hash() { # $1 = root .als path
  local seen="" queue="$1" cur deps d
  while [ -n "$queue" ]; do
    cur=$(printf '%s\n' "$queue" | head -1); queue=$(printf '%s\n' "$queue" | tail -n +2)
    case " $seen " in *" $cur "*) continue ;; esac
    seen="$seen $cur"
    deps=$(grep -E '^open [a-z]' "$cur" 2>/dev/null | awk '{print $2}' \
           | sed 's|\[.*||; s|$|.als|; s|^|alloy/|')
    for d in $deps; do [ -f "$d" ] && queue=$(printf '%s\n%s' "$queue" "$d"); done
  done
  # shellcheck disable=SC2086
  cat $seen | shasum -a 256 | awk '{print substr($1,1,16)}'
}

soak_roots() { # tier order: lemmas, sliced, then the transitional tests/
  { find alloy/soak -path '*/lemmas/*' -name '*.als' | sort
    find alloy/soak -path '*/sliced/*' -name '*.als' | sort
    find alloy/soak -path '*/tests/*'  -name '*.als' | sort; } 2>/dev/null
}

tier_of() { case "$1" in */lemmas/*) echo 0;; */sliced/*) echo 1;; *) echo 2;; esac; }

# ── plan ─────────────────────────────────────────────────────────────────────────────
cmd_plan() {
  local batch="$1" est=alloy/soak/estimates.tsv root h tier c e
  mkdir -p "$batch/cmd"
  : > "$batch/plan.unsorted"
  for root in $(soak_roots); do
    h=$(cone_hash "$root"); tier=$(tier_of "$root")
    for c in $(grep -E '^[[:space:]]*(run|check)[[:space:]]+[A-Za-z_][A-Za-z_0-9]*' "$root" | awk '{print $2}'); do
      e=-1
      [ -f "$est" ] && e=$(awk -F'\t' -v c="$c" -v h="$h" '$1==c && $2==h {print $3; exit}' "$est")
      [ -n "$e" ] || e=-1
      printf '%s\t%s\t%s\t%s\t%s\n' "$tier" "$root" "$c" "$h" "$e" >> "$batch/plan.unsorted"
    done
  done
  # order: tier asc, then estimate DESC (heaviest first; unknown -1 sorts last), then name
  sort -t"$(printf '\t')" -k1,1n -k5,5nr -k3,3 "$batch/plan.unsorted" > "$batch/plan.tsv"
  rm -f "$batch/plan.unsorted"
  echo "plan: $(wc -l < "$batch/plan.tsv" | tr -d ' ') commands -> $batch/plan.tsv"
}

# ── chunk (the dispatcher) ───────────────────────────────────────────────────────────
launch_one() { # $1 batch  $2 root  $3 command  $4 scope_hash
  local batch="$1" root="$2" c="$3" h="$4"
  mkdir -p "$batch/cmd/$c.d"
  printf 'start\t%s\nscope_hash\t%s\nroot\t%s\n' "$(date +%s)" "$h" "$root" > "$batch/cmd/$c.meta"
  nohup sh -c "java -jar '$ALLOY_JAR' -D info exec $ALLOY_FLAGS -c '$c' -o '$batch/cmd/$c.d' -f '$root' \
                 > '$batch/cmd/$c.log' 2>&1; \
               echo \$? > '$batch/cmd/$c.rc'; \
               printf 'end\t%s\n' \"\$(date +%s)\" >> '$batch/cmd/$c.meta'" \
       >/dev/null 2>&1 &
  echo "$!" > "$batch/cmd/$c.pid"
  echo "$(date '+%H:%M:%S') DISPATCH $c (root $root, pid $(cat "$batch/cmd/$c.pid"))" | tee -a "$batch/dispatch.log"
}

running_count() { # jobs with a pid file, no rc yet, process alive
  local batch="$1" n=0 p
  for p in "$batch"/cmd/*.pid; do
    [ -f "$p" ] || continue
    local c; c=$(basename "$p" .pid)
    [ -f "$batch/cmd/$c.rc" ] && continue
    kill -0 "$(cat "$p")" 2>/dev/null && n=$((n+1))
  done
  echo "$n"
}

cmd_chunk() {
  local batch="$1" window="$2" par="$3" lenient="$4"
  [ -f "$batch/plan.tsv" ] || die "no plan.tsv in $batch (run plan first)"
  local start end now remaining
  start=$(date +%s); end=$((start + window))
  echo "$(date '+%H:%M:%S') CHUNK start window=${window}s par=$par lenient=$lenient" | tee -a "$batch/dispatch.log"
  while :; do
    now=$(date +%s); remaining=$((end - now))
    # fold: revert dead 'running' rows (killed mid-solve) to pending is implicit — a pid
    # with no rc and no live process simply becomes dispatchable again on RESUME, and its
    # second death is visible in dispatch.log for the over-window judgment.
    local active; active=$(running_count "$batch")
    if [ "$remaining" -gt 0 ] && [ "$active" -lt "$par" ]; then
      local dispatched=0
      while IFS=$(printf '\t') read -r tier root c h e; do
        [ -f "$batch/cmd/$c.rc" ] && continue           # done (this batch)
        [ -f "$batch/cmd/$c.pid" ] && kill -0 "$(cat "$batch/cmd/$c.pid")" 2>/dev/null && continue  # running
        if [ "$e" -ge 0 ]; then
          [ $((e * MARGIN_NUM)) -le "$remaining" ] || { echo "$(date '+%H:%M:%S') DEFER $c est=${e}s remaining=${remaining}s" >> "$batch/dispatch.log"; continue; }
        else
          [ "$remaining" -gt "$UNKNOWN_FLOOR" ] || { echo "$(date '+%H:%M:%S') DEFER $c est=unknown remaining=${remaining}s" >> "$batch/dispatch.log"; continue; }
        fi
        launch_one "$batch" "$root" "$c" "$h"; dispatched=1; break
      done < "$batch/plan.tsv"
      # nothing dispatchable and nothing running and window still open -> all done or all deferred
      if [ "$dispatched" -eq 0 ] && [ "$active" -eq 0 ]; then
        local pending; pending=$(awk -F'\t' '{print $3}' "$batch/plan.tsv" | while read -r c; do [ -f "$batch/cmd/$c.rc" ] || echo "$c"; done | wc -l | tr -d ' ')
        echo "$(date '+%H:%M:%S') CHUNK idle: 0 running, $pending pending (deferred for window)" | tee -a "$batch/dispatch.log"
        break
      fi
    fi
    if [ "$remaining" -le 0 ]; then
      if [ "$active" -eq 0 ]; then
        echo "$(date '+%H:%M:%S') CHUNK window closed, nothing running" | tee -a "$batch/dispatch.log"; break
      fi
      echo "$(date '+%H:%M:%S') WINDOW END with $active still solving (lenient=$lenient) — over-runners left for the human kill/extend decision:" | tee -a "$batch/dispatch.log"
      for p in "$batch"/cmd/*.pid; do
        local c; c=$(basename "$p" .pid)
        [ -f "$batch/cmd/$c.rc" ] && continue
        kill -0 "$(cat "$p")" 2>/dev/null && echo "  RUNNING $c (pid $(cat "$p"))" | tee -a "$batch/dispatch.log"
      done
      [ "$lenient" = "1" ] && exit 0 || exit 1
    fi
    sleep "$POLL"
  done
  cmd_status "$batch"
}

# ── status (materialize the ledger) ──────────────────────────────────────────────────
cmd_status() {
  local batch="$1"
  [ -f "$batch/plan.tsv" ] || die "no plan.tsv in $batch"
  printf 'tier\troot\tcommand\tscope_hash\testimate_s\tstatus\telapsed_s\n' > "$batch/ledger.tsv"
  local nd=0 nm=0 ne=0 nr=0 np=0
  while IFS=$(printf '\t') read -r tier root c h e; do
    local st="pending" el=""
    if [ -f "$batch/cmd/$c.rc" ]; then
      local rc; rc=$(cat "$batch/cmd/$c.rc")
      local s0 s1; s0=$(awk -F'\t' '$1=="start"{print $2}' "$batch/cmd/$c.meta" 2>/dev/null)
      s1=$(awk -F'\t' '$1=="end"{print $2}' "$batch/cmd/$c.meta" 2>/dev/null)
      [ -n "$s0" ] && [ -n "$s1" ] && el=$((s1 - s0))
      if grep -q "against expectation" "$batch/cmd/$c.log" 2>/dev/null; then st="MISMATCH"; nm=$((nm+1))
      elif [ "$rc" != "0" ] || grep -qE "Syntax error|\[main\] ERROR" "$batch/cmd/$c.log" 2>/dev/null; then st="ERROR"; ne=$((ne+1))
      else st="done"; nd=$((nd+1)); fi
    elif [ -f "$batch/cmd/$c.pid" ] && kill -0 "$(cat "$batch/cmd/$c.pid")" 2>/dev/null; then
      st="running"; nr=$((nr+1))
      el=$(( $(date +%s) - $(awk -F'\t' '$1=="start"{print $2}' "$batch/cmd/$c.meta") ))
    else np=$((np+1)); fi
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$tier" "$root" "$c" "$h" "$e" "$st" "$el" >> "$batch/ledger.tsv"
  done < "$batch/plan.tsv"
  echo "== $batch: done=$nd mismatch=$nm error=$ne running=$nr pending=$np"
  [ "$nm" -gt 0 ] && { echo "MISMATCHES (a law may have a counterexample past the gate scopes):"; awk -F'\t' '$6=="MISMATCH"{print "  "$3"  ("$2")"}' "$batch/ledger.tsv"; }
  column -t -s "$(printf '\t')" "$batch/ledger.tsv" | sed 's/^/  /'
}

case "${1:-}" in
  plan)   shift; cmd_plan "$@";;
  chunk)  shift; cmd_chunk "$@";;
  status) shift; cmd_status "$@";;
  *) die "usage: soak-chunk.sh plan|chunk|status <batch-dir> [args]";;
esac
