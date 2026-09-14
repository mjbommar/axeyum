#!/usr/bin/env bash
# Build this lane's binary from scratch in an EMPTY target dir on this branch,
# and verify it is newer than every crates/**/*.rs before it may be used.
#
# Cargo decides freshness by MTIME. A stale prebuilt binary has produced a false
# ABSENT four times in this repository, and snapshot paths here are REUSED
# across sessions -- so the target dir is removed rather than reused, and the
# `find -newer` guard below is what licenses the binary, not the build's exit
# status.
#
# Usage: build.sh <tag>       (tag names the arm: `probe`, `lever`, ...)
set -eu
LANE_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
TAG="${1:-probe}"
TARGET=/data0/axeyum/round-head-target-$TAG
OUT=/nas3/data/axeyum/harness/round-head/bin

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
ls -la --time-style=full-iso "$OUT/smtcomp_cli-$TAG"
echo "BUILD-OK $TAG $(git rev-parse HEAD)"
