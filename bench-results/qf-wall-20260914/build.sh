#!/usr/bin/env bash
# QF-WALL -- build this lane's binary in an EMPTY target dir and verify it is
# newer than every crates/**/*.rs before it may be used. Snapshot/target paths
# are REUSED here, so exit 0 does not license a binary; `find -newer` does.
set -eu
LANE_ROOT=/home/mjbommar/projects/personal/axeyum/.claude/worktrees/agent-afa3f9f8cdbb60216
TAG="${1:-qfwall}"
TARGET=/data0/axeyum/qf-wall-target-$TAG
OUT=/nas3/data/axeyum/harness/qf-wall/bin

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
