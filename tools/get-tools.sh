#!/usr/bin/env bash
#
# Fetch pinned analysis tools into this repo's gitignored tools/ directory.
#
#   - Alloy Analyzer (used by ../alloy/*.als)
#   - ROBOT          (consult the vendored public standards under ../owl/imports/)
#
# Resolution order per tool (idempotent, SHA-256 verified):
#   1. tools/<name>.jar already present & matching  -> done
#   2. ~/tools/<name>/<name>.jar present & matching  -> symlink it (no download)
#   3. otherwise                                     -> download the pinned release
#
set -euo pipefail
REPO_TOOLS="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# name  sha256  url  shared-fallback-path
fetch() {
  local name="$1" sha="$2" url="$3" fallback="$4"
  local dest="$REPO_TOOLS/$name.jar"

  if [ -e "$dest" ] && echo "$sha  $dest" | shasum -a 256 -c - >/dev/null 2>&1; then
    echo "✓ $name.jar present and verified"; return
  fi
  if [ -f "$fallback" ] && echo "$sha  $fallback" | shasum -a 256 -c - >/dev/null 2>&1; then
    ln -sf "$fallback" "$dest"
    echo "✓ $name.jar reused from $fallback (symlinked)"; return
  fi
  echo "↓ downloading $name.jar from $url"
  curl -fsSL -o "$dest.tmp" "$url"
  if ! echo "$sha  $dest.tmp" | shasum -a 256 -c - >/dev/null 2>&1; then
    rm -f "$dest.tmp"
    echo "✗ checksum mismatch for $name.jar — refusing to install" >&2
    exit 1
  fi
  mv "$dest.tmp" "$dest"
  echo "✓ $name.jar downloaded and verified"
}

# --- Pinned versions (bump version AND sha256 together) ---

# Alloy 6.2.0
fetch alloy \
  6b8c1cb5bc93bedfc7c61435c4e1ab6e688a242dc702a394628d9a9801edb78d \
  https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.2.0/org.alloytools.alloy.dist.jar \
  "$HOME/tools/alloy/alloy.jar"

# ROBOT 1.9.10
fetch robot \
  16a73c074f3df359a7338a84b4e0788785fe06117f931bb9796e9619ea776105 \
  https://github.com/ontodev/robot/releases/download/v1.9.10/robot.jar \
  "$HOME/tools/robot/robot.jar"

echo "Tools ready in $REPO_TOOLS"
