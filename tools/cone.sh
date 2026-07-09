#!/usr/bin/env bash
# cone.sh <file.als> — print the transitive open-cone of an .als file (the file itself first).
# The same walk as `make profiles` (BFS over `^open` statements); parameterized opens have
# their [..] instantiation stripped. Used by `make check-affected` and `make check-budget`.
set -euo pipefail
[ $# -eq 1 ] || { echo "usage: tools/cone.sh <file.als>" >&2; exit 2; }
seen=" "
queue="$1"
while [ -n "$queue" ]; do
  cur=$(printf '%s\n' "$queue" | head -1)
  queue=$(printf '%s\n' "$queue" | tail -n +2)
  [ -n "$cur" ] || continue
  case "$seen" in *" $cur "*) continue;; esac
  seen="$seen$cur "
  printf '%s\n' "$cur"
  deps=$(grep -E '^open [a-z]' "$cur" 2>/dev/null | awk '{print $2}' | sed 's|\[.*||; s|$|.als|; s|^|alloy/|') || true
  for d in $deps; do
    [ -f "$d" ] && queue=$(printf '%s\n%s' "$queue" "$d")
  done
done
