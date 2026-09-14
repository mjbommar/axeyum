#!/usr/bin/env bash
# Build the lane binary from scratch in an EMPTY, LANE-PRIVATE target dir on this
# branch, and verify it is newer than every crates/**/*.rs before it may be used.
#
# Cargo decides freshness by MTIME; a stale prebuilt binary has produced a false
# ABSENT four times in this repository.  The target and output paths are
# lane-private on purpose: the `ufnia-uflia` lane's build.sh writes
# /nas3/.../harness/ufnia-uflia/bin/, and two lanes writing one binary path is
# the multi-agent failure this repository has paid for repeatedly.
#
# Usage: build.sh <tag>       (tag names the arm: `base`, `lever`, ...)
set -eu
LANE_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
TAG="${1:-base}"
TARGET=/data0/axeyum/inst-select-target-$TAG
OUT=/nas3/data/axeyum/harness/inst-select/bin

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
