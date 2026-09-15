#!/usr/bin/env bash
# SILENT-HANG -- build this lane's binary in an EMPTY target dir and verify by
# `find -newer` that no crates/**/*.rs postdates it.  Snapshot/target paths are
# REUSED on this box, so exit 0 does NOT license a binary; only the freshness
# check does.  Built with full debug symbols in release so `perf` can resolve
# frames -- a stripped release binary profiles as one unnamed address range,
# which is the shape that gets read as "nothing is running".
set -eu
LANE_ROOT=/home/mjbommar/projects/personal/axeyum/.claude/worktrees/agent-a567f41a664e53536
TAG="${1:-sh}"
TARGET=/data0/axeyum/silent-hang-target-$TAG
OUT=/nas3/data/axeyum/harness/silent-hang/bin

rm -rf "$TARGET"
mkdir -p "$TARGET" "$OUT"
cd "$LANE_ROOT"
CARGO_PROFILE_RELEASE_DEBUG=2 CARGO_PROFILE_RELEASE_STRIP=none \
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
