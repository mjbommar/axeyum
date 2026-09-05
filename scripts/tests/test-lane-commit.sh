#!/usr/bin/env bash
# Controls for `scripts/lane-commit.sh`, in a throwaway repo.
#
# Six cases, one per failure this session actually produced:
#
#   1. a rename with only ONE side named  -> refused    (the too-NARROW pathspec
#      that committed four ADR deletions without their replacements)
#   2. a sibling lane's untracked file present but not named -> NOT committed
#      (the too-WIDE pathspec that swept two lanes' new files)
#   3. the honest case -> committed, and the shared index left clean
#
# Case 2 is the one the repository's documented assertion cannot express: it
# compares the staged set against the pathspec, so it passes whenever both are
# wrong together, which is what happened twice.
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2
HELPER="$PWD/scripts/lane-commit.sh"
# The `cd` above pins this to the helper in THIS checkout, so a mutation run
# against another copy needs a scratch tree pairing that helper with this
# file. A missing helper would make every "refused" case pass vacuously (exit
# 127 looks exactly like a refusal to a status-only assertion), so fail loudly.
[ -x "$HELPER" ] || { echo "test-lane-commit: no executable helper at $HELPER" >&2; exit 2; }

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
fail=0
ok()  { echo "ok   $1"; }
bad() { echo "FAIL $1"; fail=1; }

cd "$WORK" || exit 2
git init -q .
git config user.email t@t; git config user.name t
mkdir -p .git/hooks   # no commit-msg hook here: the Agent: trailer is not under test
echo one > a.txt; echo two > b.txt
git add -A; git commit -qm base
export AXEYUM_AGENT=test-lane
printf 'subject\n\nbody\n' > "$WORK/msg"

# --- 1. half a rename is refused -------------------------------------------
git mv a.txt a-renamed.txt
out=$("$HELPER" --dry-run -- a-renamed.txt 2>&1); rc=$?
case "$rc:$out" in
  0:*) bad "1 half a rename was ACCEPTED" ;;
  *"did not name them"*|*"REFUSING"*) ok "1 half a rename refused" ;;
  *) bad "1 refused with an unexpected message: $out" ;;
esac
# naming both sides is accepted
out=$("$HELPER" --dry-run -- a.txt a-renamed.txt 2>&1); rc=$?
[ "$rc" = 0 ] && ok "1b naming both sides of the rename is accepted" \
  || bad "1b both sides refused: $out"
git mv a-renamed.txt a.txt   # restore

# --- 2. a sibling's untracked file is never swept --------------------------
echo mine > mine.txt
echo theirs > sibling-untracked.txt          # another lane's work in progress
out=$("$HELPER" -m "$WORK/msg" -- mine.txt 2>&1); rc=$?
if [ "$rc" != 0 ]; then
  bad "2 the honest commit was refused: $out"
elif git cat-file -e "HEAD:sibling-untracked.txt" 2>/dev/null; then
  bad "2 a sibling lane's untracked file was COMMITTED"
elif ! git cat-file -e "HEAD:mine.txt" 2>/dev/null; then
  bad "2 my own file did not make it into HEAD"
else
  ok "2 sibling's untracked file left alone; mine committed"
fi

# --- 3. the shared index is left clean for the committed paths -------------
unset GIT_INDEX_FILE
if [ -z "$(git diff --cached --name-only HEAD -- mine.txt)" ]; then
  ok "3 no staged revert left behind for the committed path"
else
  bad "3 the shared index still differs from HEAD for mine.txt"
fi

# --- 4. naming a path that is not dirty is refused, not silently committed --
out=$("$HELPER" --dry-run -- b.txt 2>&1); rc=$?
case "$rc:$out" in
  0:*) bad "4 naming an unchanged path was accepted" ;;
  *"did not stage"*) ok "4 naming an unchanged path refused" ;;
  *) bad "4 refused with an unexpected message: $out" ;;
esac

# --- 5. naming a DIRECTORY that contains a sibling's file is refused --------
# The "extra staged" guard is unreachable when every named path is an explicit
# file -- `git add -A -- <file>` cannot stage anything else. It fires on the case
# that actually happened: a pathspec naming a DIRECTORY, which sweeps whatever
# else is in it. Without this case that guard could be deleted with the suite
# still green, which is the failure mode it exists to prevent.
mkdir -p shared
echo mine2 > shared/mine2.txt
echo theirs2 > shared/sibling2.txt
out=$("$HELPER" --dry-run -- shared 2>&1); rc=$?
case "$rc:$out" in
  0:*) bad "5 naming a directory containing a sibling's file was ACCEPTED" ;;
  *"did not name them"*) ok "5 directory pathspec sweeping a sibling refused" ;;
  *) bad "5 refused with an unexpected message: $out" ;;
esac
# ...and naming both files explicitly is fine.
out=$("$HELPER" --dry-run -- shared/mine2.txt shared/sibling2.txt 2>&1); rc=$?
[ "$rc" = 0 ] && ok "5b naming both explicitly is accepted" \
  || bad "5b explicit naming refused: $out"

# --- 6. the helper works inside a LINKED WORKTREE ---------------------------
# `.git` there is a FILE (`gitdir: …`), not a directory, so a private-index path
# built as `$PWD/.git/index-<lane>` is not a path at all and `read-tree` fails
# with `Not a directory`. EVERY dispatched lane runs in a linked worktree, so
# this was not an edge case: the documented helper exited 3 for all of them and
# they silently fell back to plain `git commit`, which is the shared-index
# hazard the helper exists to remove. Discovered by a lane reporting it as an
# aside, not by any gate.
cd "$WORK" || exit 2
git worktree add -q --detach "$WORK/wt" HEAD 2>/dev/null
cd "$WORK/wt" || exit 2
echo linked >> a.txt
out=$("$HELPER" -m "$WORK/msg" -- a.txt 2>&1); rc=$?
if [ "$rc" = 0 ] && [ "$(git log --oneline -1 | grep -vc base)" != 0 ]; then
  ok "6 lane-commit works in a linked worktree"
else
  bad "6 lane-commit failed in a linked worktree (rc=$rc): $out"
fi
# and the private index landed in the WORKTREE's own gitdir, not a bogus path
if [ -f "$(git rev-parse --git-dir)/index-$AXEYUM_AGENT" ]; then
  ok "6b private index lives in the worktree's own gitdir"
else
  bad "6b private index was not created in the worktree gitdir"
fi
cd "$WORK" || exit 2

# --- 7. a merge in progress (somebody else's) refuses the commit ------------
# The 2026-09-05 incident: a sibling session's `git merge` stopped on a `UU`
# conflict in the shared checkout; a one-file commit through this helper became
# a MERGE commit with their branch as second parent and none of its content,
# and consumed MERGE_HEAD. The helper must refuse while MERGE_HEAD exists, in
# --dry-run as well, and accept again once the merge is gone.
# Asserted on the OUTCOME, not on a message: the unguarded helper's dry run
# accepted this and its real commit produced a two-parent commit -- and git
# prints its own "MERGE_HEAD exists" in other paths, so a message match cannot
# tell the guard from git. A fresh repo, so cases 1-6 leave nothing behind.
WORK7="$WORK/merge-in-progress"; mkdir -p "$WORK7"; cd "$WORK7" || exit 2
git init -q .; git config user.email t@t; git config user.name t; mkdir -p .git/hooks
echo one > a.txt; echo two > b.txt; git add -A; git commit -qm base
git checkout -q -b sibling; echo sibling-side > b.txt; git commit -qam sibling
git checkout -q -; echo main-side > b.txt; git commit -qam main-side
git merge -q sibling >/dev/null 2>&1 || true        # stops on the b.txt conflict
git rev-parse -q --verify MERGE_HEAD >/dev/null || bad "7 fixture: MERGE_HEAD was not set up"
head_before=$(git rev-parse HEAD)
echo mine > mine7.txt
out=$("$HELPER" -m "$WORK/msg" -- mine7.txt 2>&1); rc=$?
# Outcome AND the helper's own refusal line: outcome alone is vacuous when the
# helper never ran (a wrong $PWD gave exit 127, HEAD "unmoved", and a green
# case 7 on the first draft of this control).
case "$out" in *"REFUSING -- MERGE_HEAD exists"*) refused=1 ;; *) refused=0 ;; esac
if [ "$rc" != 0 ] && [ "$refused" = 1 ] && [ "$(git rev-parse HEAD)" = "$head_before" ] \
   && git rev-parse -q --verify MERGE_HEAD >/dev/null; then
  ok "7 a commit during another merge is refused: HEAD unmoved, MERGE_HEAD intact"
else
  bad "7 a commit during another merge went through (rc=$rc, parents=$(git log -1 --format=%P | wc -w), MERGE_HEAD=$(git rev-parse -q --verify MERGE_HEAD || echo gone)): $out"
fi
git merge --abort
out=$("$HELPER" --dry-run -- mine7.txt 2>&1); rc=$?
[ "$rc" = 0 ] && ok "7b accepted again once the merge is gone" \
  || bad "7b still refused after merge --abort: $out"
cd "$WORK" || exit 2

if [ "$fail" = 0 ]; then echo "LANE_COMMIT_CONTROLS|ok"; else echo "LANE_COMMIT_CONTROLS|FAILED" >&2; fi
exit "$fail"
