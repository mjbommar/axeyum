#!/usr/bin/env bash
# QUANT-ACTIVATION -- run one test suite INTERLEAVED on the base snapshot and on
# this branch, back to back on the same box, N times.
#
# CLAUDE.md's method: load cancels in the DIFFERENCE and not in the totals, and
# a suite that fails on the branch and passes on the base at different moments
# is not a comparison. Both arms are also reported with the load at their start,
# so a run taken in a different reference frame can be recognised as one.
#
#   qa-interleave.sh <base-worktree> <branch-worktree> <suite> [reps]
set -u
BASE="$1"; BRANCH="$2"; SUITE="$3"; REPS="${4:-2}"
for r in $(seq 1 "$REPS"); do
  for side in base branch; do
    case "$side" in
      base) W="$BASE" ;;
      *)    W="$BRANCH" ;;
    esac
    load=$(cut -d' ' -f1 /proc/loadavg)
    out=$(cd "$W" && scripts/cargo-serialized.sh test -p axeyum-solver --features full \
            --test "$SUITE" 2>&1 | grep -E '^test result:' | tail -1)
    printf 'rep%s %-6s load_start=%-6s %s\n' "$r" "$side" "$load" "${out:-NO RESULT LINE (an absent result line is an OOM, not a pass)}"
  done
done
