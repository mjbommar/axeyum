#!/usr/bin/env bash
# Build one arm's binary from THIS worktree into a named slot, and refuse to
# hand it over unless it is newer than every crates/**/*.rs.
#
# Cargo decides freshness by MTIME, and a stale prebuilt binary reported a false
# ABSENT four separate times in this repository on 2026-09-12 -- so the
# freshness check is part of the build, not a thing to remember afterwards.
#
# Usage: build.sh <arm-name>        e.g. build.sh baseline / build.sh nested
set -eu
ARM="${1:?usage: build.sh <arm-name>}"
LANE_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
TARGET="${TARGET:-/data0/axeyum/nested-array-ir-target}"
OUT=/nas3/data/axeyum/harness/nested-array-ir/bin

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

cp "$BIN" "$OUT/smtcomp_cli.$ARM"
git -C "$LANE_ROOT" rev-parse HEAD > "$OUT/smtcomp_cli.$ARM.sha"
ls -la "$OUT/smtcomp_cli.$ARM"
echo "BUILD-OK $ARM $(cat "$OUT/smtcomp_cli.$ARM.sha")"
