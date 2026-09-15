#!/usr/bin/env bash
# SILENT-HANG -- a SECOND binary, identical but with frame pointers, for stack
# attribution only.
#
# Why this exists, stated so nobody reads a number off the wrong binary:
#
#   * `gdb` cannot be used here.  `/proc/sys/kernel/yama/ptrace_scope` is `1`
#     on this host, which permits a ptrace attach only from an ANCESTOR, and a
#     sampler script's gdb is a SIBLING of the solver it wants to read.  Every
#     attempt returns "Could not attach to process".  That is a property of the
#     host, not of the solver, and it is recorded here rather than worked around
#     silently.
#   * `perf --call-graph=dwarf` resolves LEAF symbols on the default binary but
#     truncates the caller chain, so it can say the evaluator is hot and cannot
#     say who called it.  The caller is the whole question.
#   * With frame pointers, `perf --call-graph=fp` walks the chain with no
#     ptrace and no DWARF, and the callers are exact.
#
# Frame pointers cost a register and a few percent of speed.  **This binary is
# for ATTRIBUTION ONLY -- never quote a time or a verdict count from it.**  The
# verdicts and the census come from `build.sh`'s binary.
set -eu
LANE_ROOT=/home/mjbommar/projects/personal/axeyum/.claude/worktrees/agent-a567f41a664e53536
TAG=fp
TARGET=/data0/axeyum/silent-hang-target-$TAG
OUT=/nas3/data/axeyum/harness/silent-hang/bin

rm -rf "$TARGET"
mkdir -p "$TARGET" "$OUT"
cd "$LANE_ROOT"
RUSTFLAGS="-C force-frame-pointers=yes" \
CARGO_PROFILE_RELEASE_DEBUG=2 CARGO_PROFILE_RELEASE_STRIP=none \
CARGO_TARGET_DIR="$TARGET" scripts/cargo-serialized.sh build --release \
  -p axeyum-bench --example smtcomp_cli

BIN="$TARGET/release/examples/smtcomp_cli"
[ -x "$BIN" ] || { echo "ABORT: $BIN not built"; exit 2; }
STALE="$(find crates -name '*.rs' -newer "$BIN" | head -5)"
if [ -n "$STALE" ]; then
  echo "ABORT: sources newer than the binary:"; printf '%s\n' "$STALE"; exit 3
fi
echo "FRESH: no crates/**/*.rs is newer than $BIN"
cp "$BIN" "$OUT/smtcomp_cli-$TAG"
sha256sum "$OUT/smtcomp_cli-$TAG"
echo "BUILD-OK $TAG $(git rev-parse HEAD)"
