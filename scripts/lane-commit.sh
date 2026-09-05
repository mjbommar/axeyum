#!/usr/bin/env bash
# Commit exactly your own paths from a shared checkout, and prove it BOTH ways.
#
# WHY, measured on 2026-08-18 in one session by one agent:
#
#   1. Pathspec too NARROW. `git status --porcelain --untracked-files=no` was used
#      to derive the pathspec after a `git mv`. The renamed-to files are untracked
#      in a freshly `read-tree`'d private index, so they were omitted: the commit
#      landed four ADR DELETIONS with none of the additions, 705 lines removed and
#      243 added, and four decisions were briefly absent from history while every
#      reference in the tree pointed at them.
#   2. Pathspec too WIDE. The remedy was `--untracked-files=all`, which in a shared
#      checkout enumerates OTHER LANES' untracked files. The next commit swept a
#      sibling lane's new example and another's pinned output file.
#
# Both commits passed the assertion CLAUDE.md recommends:
#
#     test -z "$(git diff --cached --name-only HEAD | grep -vxF "$PATHSPEC")"
#
# because it compares the staged set against the pathspec, and BOTH TIMES THE
# PATHSPEC ITSELF WAS WRONG. That check catches HEAD moving under you mid-commit
# -- a real hazard, the tenth incident -- and cannot catch a pathspec that does
# not describe your change. Nothing else did either.
#
# So this takes the paths EXPLICITLY, from you, and checks both directions:
#
#   * nothing STAGED that you did not name            (no sibling's work swept in)
#   * nothing NAMED that failed to stage              (no half-committed rename)
#   * every named path is dirty relative to HEAD      (naming a clean path is a
#                                                      sign your list is stale)
#
# It refuses on any of those rather than committing something you can inspect
# afterwards, because `git show --stat` is what everyone inspects afterwards and
# it looked plausible in both incidents above.
#
# Usage:
#   scripts/lane-commit.sh -m <msgfile> -- <path>...
#   scripts/lane-commit.sh --dry-run -- <path>...   # check the set, commit nothing
#   git status --porcelain | grep '^ M crates/mine' | ... | xargs scripts/lane-commit.sh ...
#
# A rename must name BOTH sides. That is the point: `git mv a b` then naming only
# `b` is incident 1, and naming only `a` deletes your own file.
set -uo pipefail
# The repository you are STANDING IN, not the one this script lives in. Those
# differ when a lane runs the helper from a `scripts/lane-snapshot.sh` tree, and
# hardcoding the script's parent silently committed to the wrong checkout in the
# first draft -- every pathspec came back "did not match any files".
TOP=$(git rev-parse --show-toplevel 2>/dev/null) || {
  echo "lane-commit: not inside a git worktree" >&2; exit 2; }
cd "$TOP" || exit 2

MSG_FILE=""
DRY=0
while [ $# -gt 0 ]; do
  case "$1" in
    -m|--message-file) MSG_FILE="$2"; shift 2 ;;
    --dry-run) DRY=1; shift ;;
    --) shift; break ;;
    *) echo "lane-commit: unknown option $1" >&2; exit 2 ;;
  esac
done

if [ "$#" -eq 0 ]; then
  echo "lane-commit: name the paths explicitly after --" >&2
  exit 2
fi
if [ "$DRY" = 0 ] && [ -z "$MSG_FILE" ]; then
  echo "lane-commit: -m <file> is required (a heredoc file, not -m '...': " \
       "double quotes run backticks as commands and this repo's messages are " \
       "full of backticked identifiers)" >&2
  exit 2
fi
if [ -z "${AXEYUM_AGENT:-}" ]; then
  echo "lane-commit: export AXEYUM_AGENT=<lane> first; hooks/commit-msg refuses" \
       "an unidentified commit and lane identity must not live in git config" >&2
  exit 2
fi

WANT=$(printf '%s\n' "$@" | LC_ALL=C sort -u)

# A private index, refreshed and staged and committed in ONE process, because a
# refresh in an earlier shell invocation is already stale (incidents 8 and 9).
# `git rev-parse --git-dir`, NOT `$PWD/.git`: in a LINKED WORKTREE `.git` is a
# FILE containing `gitdir: …`, so `$PWD/.git/index-<lane>` is not a path and
# `read-tree` dies with `Not a directory`. Every dispatched lane runs in a
# linked worktree, so the documented helper failed for all of them (exit 3) and
# they fell back to plain `git commit`. `--git-dir` returns the per-worktree
# gitdir there and `.git` in the main checkout, which is right in both.
GITDIR=$(git rev-parse --git-dir) || exit 3

# A merge (or rebase, cherry-pick, revert) IN PROGRESS in this checkout belongs
# to somebody else, and `git commit` under MERGE_HEAD always produces a MERGE
# commit, whatever index it is handed. Measured 2026-09-05: a one-file PLAN.md
# commit through this helper, while a sibling session's merge sat on a `UU`
# conflict, landed as a merge commit with parents (main, their branch tip) and a
# tree carrying NONE of their branch's content -- their lane was recorded as
# merged and dropped in one commit, and MERGE_HEAD was consumed so their own
# `git commit` could no longer finish the merge. Every guard below passed,
# because the pathspec was right; the state of the REPOSITORY was wrong. So
# this refuses first, in `--dry-run` too, since a dry run that says "fine" is
# the last thing read before the real one.
for inprog in MERGE_HEAD CHERRY_PICK_HEAD REVERT_HEAD; do
  if git rev-parse -q --verify "$inprog" >/dev/null 2>&1; then
    echo "lane-commit: REFUSING -- $inprog exists: a merge/cherry-pick/revert is in" >&2
    echo "  progress in this checkout (another lane's, if you did not start one)." >&2
    echo "  A commit now would become a MERGE commit that records that branch as" >&2
    echo "  merged with none of its content. Wait for it to finish, or abort YOUR" >&2
    echo "  OWN one; never touch another lane's." >&2
    exit 6
  fi
done
if [ -d "$GITDIR/rebase-merge" ] || [ -d "$GITDIR/rebase-apply" ]; then
  echo "lane-commit: REFUSING -- a rebase is in progress in this checkout." >&2
  exit 6
fi

export GIT_INDEX_FILE="$GITDIR/index-$AXEYUM_AGENT"
git read-tree HEAD || exit 3
git add -A -- "$@" || exit 3

# `--no-renames` on purpose: with rename detection ON, `--name-only` prints only
# the DESTINATION of a rename, so comparing it against a pathspec that correctly
# names both sides reports the source as "did not stage".
GOT=$(git diff --cached --no-renames --name-only HEAD | LC_ALL=C sort -u)

# LC_ALL=C on the comparison too: `comm` requires both inputs sorted in the
# SAME collation and silently produces garbage otherwise. It emitted "file 1 is
# not in sorted order" on a real commit here; a warning is the lucky case.
extra=$(LC_ALL=C comm -13 <(printf '%s\n' "$WANT") <(printf '%s\n' "$GOT"))
missing=$(LC_ALL=C comm -23 <(printf '%s\n' "$WANT") <(printf '%s\n' "$GOT"))

fail=0
if [ -n "$extra" ]; then
  echo "lane-commit: REFUSING -- these staged but you did not name them." >&2
  echo "  In a shared checkout they are probably another lane's work." >&2
  printf '    %s\n' $extra >&2
  fail=1
fi
if [ -n "$missing" ]; then
  echo "lane-commit: REFUSING -- you named these but they did not stage." >&2
  echo "  Either they equal HEAD already, or this is half of a rename." >&2
  printf '    %s\n' $missing >&2
  fail=1
fi
# A rename whose OTHER HALF you did not name. `git add -A -- <new path>` stages
# the addition and says nothing about the disappearance of the old one, so the
# staged set equals the named set and both are wrong -- which is exactly how four
# ADR files were deleted with none of their replacements. Detected by asking the
# tree, not the index: a path HEAD has, that is gone from disk, whose deletion is
# not staged, sitting in a directory you are committing into.
dirs=$(printf '%s\n' "$WANT" | xargs -r -n1 dirname | sort -u)
for d in $dirs; do
  while IFS= read -r tracked; do
    [ -n "$tracked" ] || continue
    [ -e "$tracked" ] && continue
    # `grep -c`, not `grep -q`: this script runs under `set -o pipefail`, and
    # `-q` exits at the first match, SIGPIPEs `printf`, and makes the pipeline
    # 141 -- which pipefail reads as "no match". A path that IS staged would
    # then be reported as failed-to-stage, and whether that happens depends on
    # whether printf finished writing first. See CLAUDE.md, banned shell idioms.
    [ "$(printf '%s\n' "$GOT" | grep -cxF "$tracked")" -gt 0 ] && continue
    echo "lane-commit: REFUSING -- \`$tracked\` is in HEAD, gone from disk, and" >&2
    echo "  its deletion is not staged. If you renamed it, NAME BOTH SIDES; if" >&2
    echo "  another lane deleted it, this commit would land an inconsistent tree." >&2
    fail=1
  done <<< "$(git ls-tree -r --name-only HEAD -- "$d" 2>/dev/null)"
done

[ "$fail" = 0 ] || exit 4

n=$(printf '%s\n' "$GOT" | grep -c .)
echo "lane-commit: $n path(s), staged set == named set, base $(git rev-parse --short HEAD)"
if [ "$DRY" = 1 ]; then
  echo "lane-commit: --dry-run, nothing committed"
  exit 0
fi

git commit -F "$MSG_FILE" || exit 5
sha=$(git rev-parse --short HEAD)
echo "lane-commit: committed $sha"

# Resync the SHARED index for these paths only, or the next lane's bare
# `git commit` applies a staged revert of what you just landed (incident 7).
# `git hash-object` vs `git rev-parse HEAD:` rather than `git diff HEAD`: for a
# path the shared index has never seen, `git diff HEAD` reports a DELETION and
# the naive test says "differs", so you decline to restage and leave exactly the
# staged deletion you were trying to avoid.
unset GIT_INDEX_FILE
resynced=0
skipped=""
for f in $GOT; do
  if [ ! -e "$f" ]; then
    git rm -q --cached -- "$f" 2>/dev/null && resynced=$((resynced + 1))
    continue
  fi
  a=$(git hash-object "$f" 2>/dev/null)
  b=$(git rev-parse "HEAD:$f" 2>/dev/null)
  if [ "$a" = "$b" ]; then
    git add -- "$f" && resynced=$((resynced + 1))
  else
    # Another lane edited it after your commit. Point the index entry at HEAD
    # without touching their worktree -- staging their content would hand it to
    # whoever next runs a bare `git commit`.
    git reset -q HEAD -- "$f" && skipped="$skipped $f"
  fi
done
echo "lane-commit: shared index resynced for $resynced path(s)${skipped:+; reset-to-HEAD (moved under you):$skipped}"
left=$(git diff --cached --name-only HEAD -- $GOT | grep -c . || true)
if [ "$left" != 0 ]; then
  echo "lane-commit: WARNING -- $left of your paths still differ in the shared index" >&2
  exit 6
fi
exit 0
