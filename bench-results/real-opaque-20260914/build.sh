#!/usr/bin/env bash
# REAL-OPAQUE -- build this lane's binary in an EMPTY target dir and verify it is
# newer than every crates/**/*.rs before it may be used.
#
# R12: freshness by `find -newer`, not by exit status. Snapshot and target paths
# ARE reused on this box, so a fast build proves nothing about what is in the
# binary.
set -eu
LANE_ROOT=/home/mjbommar/projects/personal/axeyum/.claude/worktrees/agent-a6f68493cb26e008b
TAG="${1:-realopaque}"
TARGET=/data0/axeyum/real-opaque-target-$TAG
OUT=/nas3/data/axeyum/harness/real-opaque/bin

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
  printf '%s\n' "$STALE"; exit 3
fi
echo "FRESH: no crates/**/*.rs is newer than $BIN"
cp "$BIN" "$OUT/smtcomp_cli-$TAG"
ls -la --time-style=full-iso "$OUT/smtcomp_cli-$TAG"
sha256sum "$OUT/smtcomp_cli-$TAG"
echo "BUILD-OK $TAG $(git rev-parse HEAD)"
