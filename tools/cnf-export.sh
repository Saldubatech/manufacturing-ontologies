#!/usr/bin/env bash
# cnf-export.sh — the CNF artifact cache: export a command's Kodkod translation as
# DIMACS, gzipped and indexed. The "class files" of the model (PDEV-1609 program):
# a keyed, regenerable BUILD PRODUCT — never authoritative, rebuilt on any key miss.
#
# Key = (command, scope_hash, alloy_version). scope_hash is the root's cone hash
# (same function the soak planner uses — soak-chunk.sh conehash), so a model commit
# that does not touch a command's cone keeps its CNF valid, and any alloy.jar bump
# invalidates everything. model_sha is stamped for human browsing, not for keying.
#
# Layout (cnf/ is gitignored, like corpus/ — the manifest is the index, in place):
#   cnf/manifest.tsv                                  registered  model_sha  alloy_version  root  command  scope_hash  vars  clauses  path
#   cnf/<scope_hash>/<command>.cnf.gz                 the payload
#
# Usage: tools/cnf-export.sh <root.als> <command> [FORCE=1 to re-export an existing key]
#
# Determinism stance: Alloy's translation is not guaranteed byte-stable across runs;
# the cache promises EQUIVALENCE (same problem at the same scope), not identity. A
# verdict obtained on a cached CNF (e.g. by an external solver: UNSAT on a check's
# CNF = the law holds at that scope) transfers; a SAT assignment does NOT reconstruct
# an Alloy witness (the variable<->atom mapping is not exported).

set -u
die() { echo "cnf-export: $*" >&2; exit 2; }

root=${1:-}; cmd=${2:-}
[ -n "$root" ] && [ -n "$cmd" ] || die "usage: cnf-export.sh <root.als> <command>"
[ -f "$root" ] || die "no such root: $root"
[ -f tools/alloy.jar ] || die "tools/alloy.jar missing — run 'make tools'"

CNFDIR=${CNFDIR:-cnf}
FORCE=${FORCE:-0}

scope_hash=$(tools/soak-chunk.sh conehash "$root") || die "conehash failed for $root"
alloy_version=$(java -jar tools/alloy.jar version 2>/dev/null | head -1)
[ -n "$alloy_version" ] || alloy_version=$(shasum -a 256 tools/alloy.jar | cut -c1-12)
model_sha=$(git rev-parse --short=12 HEAD 2>/dev/null || echo unknown)
git diff --quiet 2>/dev/null || model_sha="${model_sha}+dirty"

mkdir -p "$CNFDIR/$scope_hash"
manifest="$CNFDIR/manifest.tsv"
[ -f "$manifest" ] || printf 'registered\tmodel_sha\talloy_version\troot\tcommand\tscope_hash\tvars\tclauses\tpath\n' > "$manifest"

out="$CNFDIR/$scope_hash/$cmd.cnf.gz"
if [ -f "$out" ] && [ "$FORCE" != 1 ]; then
  echo "cache hit: $out (key command+scope_hash+alloy unchanged; FORCE=1 to re-export)"
  exit 0
fi

tmp=$(mktemp -d "${TMPDIR:-/tmp}/cnf-export.XXXXXX") || die "mktemp failed"
trap 'rm -rf "$tmp"' EXIT

echo "translating $cmd from $root (scope $scope_hash, alloy $alloy_version)..."
java -jar tools/alloy.jar exec -s CNF -c "$cmd" -o "$tmp" -f "$root" || die "translation failed"

produced=$(find "$tmp" -name '*.cnf' | head -1)
[ -n "$produced" ] || die "no .cnf produced (check the command name: $cmd)"
read -r _ _ vars clauses < <(head -1 "$produced")

gzip -9 -c "$produced" > "$out" || die "gzip failed"
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
  "$(date +%s)" "$model_sha" "$alloy_version" "$root" "$cmd" "$scope_hash" "$vars" "$clauses" "$out" >> "$manifest"
echo "registered: $out ($vars vars, $clauses clauses; model $model_sha)"
