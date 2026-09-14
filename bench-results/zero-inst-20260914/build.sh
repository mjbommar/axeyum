#!/usr/bin/env bash
# ZERO-INST -- build this lane's binary from scratch in an EMPTY target dir and
# verify it is newer than every crates/**/*.rs before it may be used.
#
# Cargo decides freshness by MTIME, and snapshot/target paths here are REUSED
# across sessions, so a build that reports exit 0 can hand back a binary from an
# earlier branch. ADR-2020's copy of this guard FIRED TWICE on background builds
# that exited 0. The `find -newer` check below is what licenses the binary --
# never the build's exit status (pre-registration R13).
#
# Usage: build.sh <tag>
set -eu
LANE_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
TAG="${1:-lever}"
TARGET=/data0/axeyum/zero-inst-target-$TAG
OUT=/nas3/data/axeyum/harness/zero-inst/bin

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
