#!/usr/bin/env bash
# DT-QUANT-TRACE -- build this lane's binary in an EMPTY target dir and verify
# it is newer than every crates/**/*.rs before it may be used.
#
# Cargo decides freshness by MTIME, so a build exiting 0 can hand back a binary
# from an earlier branch (CLAUDE.md, "Commands"). The `find -newer` check is
# what licenses the binary, never the exit status.
set -eu
LANE_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
TAG="${1:-base}"
TARGET=/data0/axeyum/dt-quant-trace-target-$TAG
OUT=/nas3/data/axeyum/harness/dt-quant-trace/bin

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
