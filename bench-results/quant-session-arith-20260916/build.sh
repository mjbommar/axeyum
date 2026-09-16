#!/usr/bin/env bash
# QUANT-SESSION-ARITH (ADR-2130) -- build this lane's binary in its own target
# dir and REFUSE it unless it is newer than every crates/**/*.rs.
#
# Cargo decides freshness by MTIME, so a build that exits 0 can hand back a
# binary from an earlier branch. The `find -newer` check licenses the binary;
# the exit status does not.
set -eu
LANE_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
TAG="${1:-lane}"
TARGET=/data0/axeyum/quant-session-arith-target
OUT=/nas3/data/axeyum/harness/quant-session-arith/bin

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
echo "BUILD-OK $TAG at $(git rev-parse HEAD)"
