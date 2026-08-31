#!/usr/bin/env bash
# Format every changed .rs file BEFORE a push, by name.
#
# `hooks/pre-push` runs `cargo fmt --check` as part of a battery measured at
# ~545 s uncontended. A formatting slip therefore does not cost a rerun -- it
# costs the WHOLE battery, twice, and it happened twice in one session (two
# `assert!` calls over the line budget, then two example files). Both were
# invisible until the push had already spent its time.
#
# `cargo fmt` is workspace-wide and would sweep other lanes' work in progress,
# which this repository forbids. So this formats CHANGED files individually.
#
# --check reports without rewriting. Exit 1 if anything is (or would be)
# reformatted, so a caller can decide.
set -u
MODE="${1:---write}"
BASE="${AXEYUM_FMT_BASE:-origin/main}"
git rev-parse --verify -q "$BASE" > /dev/null || BASE="$(git rev-parse HEAD~1)"

mapfile -t FILES < <(git diff --name-only "$BASE...HEAD" -- '*.rs'; git diff --name-only -- '*.rs')
COUNT=0
TOUCHED=0
for f in $(printf '%s\n' "${FILES[@]}" | sort -u); do
  [ -f "$f" ] || continue
  COUNT=$((COUNT + 1))
  if ! rustfmt --edition 2024 --check "$f" > /dev/null 2>&1; then
    TOUCHED=$((TOUCHED + 1))
    if [ "$MODE" = "--check" ]; then
      echo "  UNFORMATTED: $f"
    else
      rustfmt --edition 2024 "$f" && echo "  formatted: $f"
    fi
  fi
done

# A sweep that examined nothing is not a clean sweep. Say which it was.
if [ "$COUNT" -eq 0 ]; then
  echo "LANE_PREPUSH_FMT|examined=0|no changed .rs files against $BASE -- nothing checked"
  exit 0
fi
echo "LANE_PREPUSH_FMT|examined=$COUNT|reformatted=$TOUCHED|base=$BASE"

# REFORMATTING LEAVES THE WORKTREE DIRTY, AND THE COMMITS STILL UNFORMATTED.
# Measured 2026-08-31: this script reformatted two files, I started a push in
# the next breath, and `hooks/pre-push` rejected it on its dirty-worktree
# guard -- correctly. The subtler hazard is the one that guard happens to
# catch for us: `cargo fmt --all --check` in the hook reads the WORKTREE,
# which this script has just fixed, while the COMMITS being pushed still hold
# the unformatted content. That is the repository's documented "green gate,
# broken commit" trap, and here it would have pushed unformatted code to main
# for CI to reject.
#
# So a run that reformatted anything exits NONZERO. Commit the result, then
# push. Exit 3 is deliberately distinct from a --check failure (1).
if [ "$MODE" != "--check" ] && [ "$TOUCHED" -gt 0 ]; then
  echo "LANE_PREPUSH_FMT|COMMIT-REQUIRED|$TOUCHED file(s) were reformatted and are UNCOMMITTED." >&2
  echo "  The push hook checks the worktree; the commits still carry the old bytes." >&2
  echo "  Commit them, then push." >&2
  exit 3
fi
[ "$TOUCHED" -eq 0 ] || [ "$MODE" != "--check" ]
