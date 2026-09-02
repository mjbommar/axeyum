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
GENERATED=(PLAN.md docs/research/09-decisions/README.md artifacts/autogenesis/frontier-shape-census-v1.json)

# A DIRTY TREE BEFORE THE MERGE GETS SWEPT INTO THE MERGE COMMIT.
# Line 44 below is `git add -A -- PLAN.md docs/ artifacts/ scripts/ crates/
# justfile`, which is right for the regenerated files a merge produces and wrong
# for anything else already modified. Measured 2026-08-31: my own uncommitted
# `scripts/lane-push.sh` edit and a `settled-fact-statement-pins.json` floor bump
# were swept into a draw-15 merge commit whose message mentions neither. Nothing
# was lost and the content was correct -- but the change is attributed to a merge
# it has nothing to do with, and `git log -- scripts/lane-push.sh` now points at
# a nursery draw.
#
# This is CLAUDE.md's pathspec hazard from the other side: the documented failure
# is a pathspec too NARROW dropping your own hunks; this is one wide enough to
# adopt someone else's. Both are silent.
#
# So: refuse to start on a dirty tree. Commit your own work first, then merge.
if [ "${LANE_MERGE_ALLOW_DIRTY:-0}" != 1 ]; then
  dirty=$(git status --porcelain --untracked-files=no)
  if [ -n "$dirty" ]; then
    echo "LANE_MERGE_LAND|DECLINING -- tracked files are modified before the merge." >&2
    printf '%s\n' "$dirty" | sed 's/^/  /' >&2
    echo "  `git add -A` after the merge would sweep these into the merge commit." >&2
    echo "  Commit them first. LANE_MERGE_ALLOW_DIRTY=1 overrides." >&2
    exit 1
  fi
fi

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
# The frontier shape census is a pure function of the fact ledger, so ANY merge
# that lands or flips a fact stales it while touching neither its script nor
# its artifact -- the first two merges after its gate landed (2026-09-02) both
# failed post-merge hygiene on exactly this. Regenerate it here like PLAN.md.
# Its exit 2 means "frontier unavailable"; the gate reports that as
# not-answerable rather than failing, so only exit 1 is a stop here.
python3 scripts/frontier-shape-census.py > /tmp/lane-merge-land.census 2>&1
census_rc=$?
if [ "$census_rc" -eq 1 ]; then
  echo "LANE_MERGE_LAND|frontier-shape-census failed" >&2; exit 1
fi

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
