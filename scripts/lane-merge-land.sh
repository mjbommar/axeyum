#!/usr/bin/env bash
# Merge a lane branch and land it -- refusing to commit when the resolver did.
#
# `lane-merge-resolve.py` exits 1 when it will not resolve a file: a JSON whose
# two sides disagree on a scalar, or a Rust hunk cut mid-item. I read that
# refusal on screen, then ran `git add -A` and committed anyway, because the
# `add` did not consult the exit status. The merge commit went in with conflict
# markers inside a JSON manifest, and `check-settled-fact-statements.py` could
# not parse its own input.
#
# That is this repository's oldest lesson turned on myself: I did not discard
# the status, I READ it and did not act on it, which is worse. The remedy is to
# put the decision in the script rather than in my attention.
#
# Usage: lane-merge-land.sh <branch>
# Exits 1 with the refused paths named and the merge LEFT IN PROGRESS, so the
# tree still shows what needs a hand.
set -u
BRANCH="${1:?usage: lane-merge-land.sh <branch>}"
GENERATED=(PLAN.md docs/research/09-decisions/README.md)

git merge --no-edit "$BRANCH" > /dev/null 2>&1
MERGE_STATUS=$?

python3 scripts/lane-merge-resolve.py
RESOLVE=$?
# 0 resolved, 2 nothing conflicted; 1 means it refused at least one file.
if [ "$RESOLVE" = "1" ]; then
  echo "LANE_MERGE_LAND|REFUSED|the resolver would not resolve every file -- NOT committing." >&2
  echo "  Rebuild the refused file from the two sides by PARSING them:" >&2
  echo "    git show :2:<path>   (ours)      git show :3:<path>   (theirs)" >&2
  echo "  The merge is left in progress so the conflict is still visible." >&2
  exit 1
fi

for g in "${GENERATED[@]}"; do
  git checkout --theirs "$g" 2>/dev/null || true
done
python3 scripts/gen-adr-index.py > /tmp/lane-merge-land.adr 2>&1 || {
  echo "LANE_MERGE_LAND|gen-adr-index failed" >&2; exit 1; }
python3 scripts/gen-plan.py > /tmp/lane-merge-land.plan 2>&1 || {
  echo "LANE_MERGE_LAND|gen-plan failed" >&2; exit 1; }

git add -A -- PLAN.md docs/ artifacts/ scripts/ crates/ justfile

REMAIN="$(git diff --name-only --diff-filter=U)"
if [ -n "$REMAIN" ]; then
  echo "LANE_MERGE_LAND|UNRESOLVED after add: $REMAIN" >&2; exit 1
fi

# The last line of defence, and the one that would have caught me: never commit
# a tracked file containing a conflict marker, whatever any earlier step said.
MARKED="$(git diff --cached --name-only | while read -r f; do
  [ -f "$f" ] && /usr/bin/grep -lE '^(<<<<<<< |=======$|>>>>>>> )' "$f" 2>/dev/null
done)"
if [ -n "$MARKED" ]; then
  echo "LANE_MERGE_LAND|CONFLICT MARKERS staged in: $MARKED -- NOT committing." >&2
  exit 1
fi

if [ -f .git/MERGE_HEAD ]; then
  git commit -q --no-edit || { echo "LANE_MERGE_LAND|commit failed" >&2; exit 1; }
fi
echo "LANE_MERGE_LAND|landed $(git rev-parse --short HEAD)|merge_status=$MERGE_STATUS"
bash scripts/check-merge-hygiene.sh
