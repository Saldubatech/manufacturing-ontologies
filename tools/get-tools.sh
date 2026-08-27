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

# name  tag  sha256(source tarball)  url  --  source-built SAT solvers (PDEV-1711):
# the BINARY cannot be checksum-pinned (build output varies per machine), so the
# TARBALL is verified and tools/.<name>-version stamps the built tag for idempotence.
fetch_build() {
  local name="$1" tag="$2" sha="$3" url="$4"
  local bin="$REPO_TOOLS/$name" marker="$REPO_TOOLS/.$name-version"
  if [ -x "$bin" ] && [ "$(cat "$marker" 2>/dev/null)" = "$tag" ]; then
    echo "✓ $name present ($tag)"; return
  fi
  local tmp; tmp=$(mktemp -d)
  echo "↓ downloading $name $tag"
  curl -fsSL -o "$tmp/src.tar.gz" "$url"
  if ! echo "$sha  $tmp/src.tar.gz" | shasum -a 256 -c - >/dev/null 2>&1; then
    rm -rf "$tmp"; echo "✗ checksum mismatch for $name — refusing to build" >&2; exit 1
  fi
  tar -xzf "$tmp/src.tar.gz" -C "$tmp"
  local srcdir; srcdir=$(find "$tmp" -maxdepth 1 -type d -name "$name-*" | head -1)
  echo "⚙ building $name ($tag)..."
  ( cd "$srcdir" && ./configure >/dev/null && make -j4 >/dev/null 2>&1 ) \
    || { rm -rf "$tmp"; echo "✗ build failed for $name" >&2; exit 1; }
  local built
  for built in "$srcdir/build/$name" "$srcdir/$name"; do [ -x "$built" ] && break; done
  [ -x "$built" ] || { rm -rf "$tmp"; echo "✗ built binary not found for $name" >&2; exit 1; }
  cp "$built" "$bin"
  echo "$tag" > "$marker"
  rm -rf "$tmp"
  echo "✓ $name built and installed ($tag)"
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

# kissat 4.0.4 — sequential SAT champion (SC2025 main-track family); consumes the
# cnf/ cache (kissat <file.cnf[.gz]>); UNSAT on a check's CNF = the law holds at scope
fetch_build kissat rel-4.0.4 \
  bfe93eaa6323b48011e4b1fcf74b3f2e20f9de544767e728009e5b2018296193 \
  https://github.com/arminbiere/kissat/archive/refs/tags/rel-4.0.4.tar.gz

# gimsatul 1.1.2 — shared-memory parallel (kissat lineage, clause sharing, DRAT in
# parallel); gimsatul --threads=N <file.cnf[.gz]>
fetch_build gimsatul rel-1.1.2 \
  9a260cd064519b83786ee39b73eb1ccaf6516923804cb98ad41a11257455cab5 \
  https://github.com/arminbiere/gimsatul/archive/refs/tags/rel-1.1.2.tar.gz

echo "Tools ready in $REPO_TOOLS"
