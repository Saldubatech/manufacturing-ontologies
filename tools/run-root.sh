#!/usr/bin/env bash
# run-root.sh <root.als> — run ONE gate root, log + instances under out/par/.
# Used by `make check-alloy-par` (BSD xargs cannot carry a long -I replacement string,
# so the per-root command lives here). Env: ALLOY_JAR (default tools/alloy.jar), ALLOY_FLAGS.
set -u
root="$1"
b=$(printf '%s' "$root" | tr '/' '_')
mkdir -p "out/par/$b.d"
# ALLOY_FLAGS is deliberately word-split (e.g. "-s glucose")
# shellcheck disable=SC2086
java -jar "${ALLOY_JAR:-tools/alloy.jar}" -D info exec ${ALLOY_FLAGS:-} -c "*" -o "out/par/$b.d" -f "$root" > "out/par/$b.log" 2>&1
echo "== $root done"
