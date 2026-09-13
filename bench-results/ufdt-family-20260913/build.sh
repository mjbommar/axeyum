#!/usr/bin/env bash
# Build the lane binary from scratch in an EMPTY target dir on this branch, and
# verify it is newer than every crates/**/*.rs before it is allowed to be used.
# Cargo decides freshness by MTIME; a stale prebuilt binary has produced a false
# ABSENT four times in this repository.
#
# Usage: build.sh <tag>       (tag names the arm: `base`, `fix`, ...)
set -eu
LANE_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
TAG="${1:-base}"
TARGET=/data0/axeyum/ufdt-family-target-$TAG
OUT=/nas3/data/axeyum/harness/ufdt-family/bin

rm -rf "$TARGET"
mkdir -p "$TARGET" "$OUT"
cd "$LANE_ROOT"
CARGO_TARGET_DIR="$TARGET" scripts/cargo-serialized.sh build --release \
  -p axeyum-bench --example smtcomp_cli

BIN="$TARGET/release/examples/smtcomp_cli"
[ -x "$BIN" ] || { echo "ABORT: $BIN not built"; exit 2; }

STALE="$(find crates -name '*.rs' -newer "$BIN" | head -5)"
if [ -n "$STALE" ]; then
  echo "ABORT: sources newer than the binary -- it does not contain this branch:"
  printf '%s\n' "$STALE"
  exit 3
fi
echo "FRESH: no crates/**/*.rs is newer than $BIN"
cp "$BIN" "$OUT/smtcomp_cli-$TAG"
ls -la "$OUT/smtcomp_cli-$TAG"
echo "BUILD-OK $TAG $(git rev-parse HEAD)"
