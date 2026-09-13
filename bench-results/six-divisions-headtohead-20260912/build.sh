#!/usr/bin/env bash
# Build the board binary from scratch in an EMPTY target dir on this branch, and
# verify it is newer than every crates/**/*.rs before it is allowed to be used.
#
# Cargo decides freshness by MTIME.  A stale prebuilt binary reported a false
# ABSENT four separate times in this repository on 2026-09-12, so the freshness
# check is part of the build, not a thing to remember afterwards.
set -eu
LANE_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
TARGET=/data0/axeyum/board-six-target
OUT=/nas3/data/axeyum/harness/six-divisions/bin

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

cp "$BIN" "$OUT/smtcomp_cli"
ls -la "$OUT/smtcomp_cli"
echo "BUILD-OK"
