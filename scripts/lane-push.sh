#!/usr/bin/env bash
# Push once, and know what it will cost BEFORE it starts.
#
# Two frictions this removes, both measured on 2026-08-19:
#
# 1. CONCURRENT PUSHES SERIALIZE ON THE HOOK'S WORKTREE LOCK, INVISIBLY.
#    `hooks/pre-push` gates a stable per-lane worktree under an flock. Two
#    pushes started ten minutes apart took 5,510 s and 9,876 s -- and the
#    second's own steps only account for ~4,900 s of that, so roughly 4,900 s
#    was spent waiting to begin, with no output at all. `git push` prints
#    nothing while it blocks, so the state is indistinguishable from a hang.
#    I did this to myself twice in one day.
#
# 2. YOU CANNOT TELL A FREE PUSH FROM AN EXPENSIVE ONE UNTIL IT IS TOO LATE.
#    The hook exits immediately when no `*.rs`/`*.toml` changed, and runs a
#    full battery when any did -- 545 s uncontended, 2,699 s for a single step
#    under lane contention. Whether you are about to pay that is a `git diff`
#    away, and nothing was telling you.
#
# Usage:
#   scripts/lane-push.sh              # check, report the cost, push
#   scripts/lane-push.sh --dry-run    # report only, and genuinely free
#
# NOTE `git push --dry-run` IS NOT FREE: it runs the pre-push hook. A `--dry-run`
# started here purely as a test fixture for the concurrency guard below ran the
# full battery for 46 minutes before anyone noticed, and blocked a real push the
# whole time. This script's own `--dry-run` never invokes git push at all.
#   scripts/lane-push.sh --force      # push even if another push is running
#   scripts/lane-push.sh --to main    # push HEAD to a DIFFERENT branch
#   scripts/lane-push.sh --to main --retry 3   # re-merge and retry on a race
#
# `--to main` exists because landing a lane's work is `git push origin HEAD:main`,
# and without a target every part of this script reasoned about the WRONG REF:
# the range, the cost estimate, and the fast-forward check were all computed
# against `origin/<current-branch>`, which is not what the push updates.
#
# The cost estimate is the reason to run this script at all, so getting it wrong
# is not cosmetic. Measured on a fixture (`scripts/tests/test-lane-push-target.sh`)
# with a session branch whose remote copy has fallen behind main -- the ordinary
# state of a branch that has merged main down since it was last pushed:
#
#     lane-push.sh            ->  2 commit(s) -> origin/feature
#                                 FULL BATTERY -- 1 Rust/TOML file(s) changed
#     lane-push.sh --to main  ->  1 commit(s) -> origin/main
#                                 FREE -- no *.rs/*.toml in the range
#
# Same push. The `.rs` it "found" was one main already has; the range against the
# stale upstream re-counts everything merged down in between. An estimate that is
# wrong in the expensive direction gets ignored, and then it is not an estimate.
#
# Exit 75 (EX_TEMPFAIL) when it declines because another push holds the lock --
# distinguishable from a rejected push, which is the point.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)" || exit 2

DRY=0; FORCE=0; TO=""; RETRY=1
while [ $# -gt 0 ]; do case "$1" in
  --dry-run) DRY=1 ;;
  --force) FORCE=1 ;;
  --to) TO="${2:-}"; [ -n "$TO" ] || { echo "lane-push: --to needs a branch" >&2; exit 2; }; shift ;;
  --retry) RETRY="${2:-}"; case "$RETRY" in ''|*[!0-9]*) echo "lane-push: --retry needs a count" >&2; exit 2 ;; esac; shift ;;
  *) echo "lane-push: unknown option $1" >&2; exit 2 ;;
esac; shift; done

branch=$(git rev-parse --abbrev-ref HEAD)
target="${TO:-$branch}"
upstream="origin/$target"
new_ref=0
if ! git rev-parse --verify -q "$upstream" >/dev/null; then
  echo "lane-push: no $upstream yet; pushing will create it"
  new_ref=1
  # Match hooks/pre-push: a new branch is measured from its fork with main,
  # not from an unresolved remote name and not across the whole repository.
  base=$(git merge-base origin/main HEAD 2>/dev/null || echo "HEAD~20")
  range="$base..HEAD"
else
  base="$upstream"
  range="$upstream..HEAD"
fi

n=$(git rev-list --count "$range" 2>/dev/null || echo 0)
if [ "$n" = 0 ] && [ "$new_ref" = 0 ]; then
  echo "lane-push: nothing to push ($branch is up to date with $upstream)"
  exit 0
fi

# What the hook will decide, computed the same way it does.
changed=$(git diff --name-only "$base" HEAD -- '*.rs' '*.toml' | wc -l)
if [ "$changed" -eq 0 ]; then
  cost="FREE — no *.rs/*.toml in the range, the hook exits before any cargo step"
else
  cost="FULL BATTERY — $changed Rust/TOML file(s) changed; 545 s uncontended, far more under lane contention"
fi
echo "lane-push: $n commit(s) from $branch -> origin/$target"
echo "lane-push: $cost"

# Another push in flight? `pgrep -x git` and not a pattern containing our own
# command line -- a `pgrep -f` for the push text matches this script and has
# killed the wrong process here before.
others=0
for p in /proc/[0-9]*; do
  [ -r "$p/comm" ] || continue
  [ "$(cat "$p/comm" 2>/dev/null)" = "git" ] || continue
  case "$(tr '\0' ' ' < "$p/cmdline" 2>/dev/null)" in *push*) others=$((others + 1)) ;; esac
done
if [ "$others" -gt 0 ] && [ "$FORCE" = 0 ]; then
  echo "lane-push: DECLINING — $others git push process(es) already running." >&2
  echo "  A second push blocks on the hook's worktree lock with NO output and no" >&2
  echo "  timeout. Wait for the first, or pass --force if you know it is unrelated." >&2
  exit 75
fi

# Non-fast-forward is worth knowing BEFORE the hook runs, not after: the hook is
# the expensive part and the remote rejects afterwards, so you pay in full for a
# push that was never going to land.
if git rev-parse --verify -q "$upstream" >/dev/null && \
   ! git merge-base --is-ancestor "$upstream" HEAD; then
  echo "lane-push: DECLINING -- origin/$target is NOT an ancestor of HEAD." >&2
  echo "  $(git rev-list --count HEAD.."$upstream") commit(s) are on it that you do not have." >&2
  echo "  Merge or rebase first; pushing would be rejected AFTER the hook has run." >&2
  exit 1
fi

# A DIRTY TRACKED WORKTREE IS WORTH KNOWING BEFORE THE HOOK, NOT AFTER IT.
# `hooks/pre-push` already refuses a dirty tree -- but it does so at the END of a
# 545-second battery, so the whole cost is paid for a push that was never going
# to land. Measured twice on 2026-08-31, both times mine: the formatter
# reformatted files, I read its exit 3 and started the push anyway, and the hook
# rejected it minutes later.
#
# The narrower hazard underneath is why this cannot be left to the hook. After
# the formatter runs, `cargo fmt --check` PASSES -- the worktree is fixed -- while
# the COMMITS being pushed still carry the old bytes. Green gate, broken commit.
# Checking for a dirty tree up front catches that and every other variant, and
# it costs milliseconds.
#
# My first draft of this guard ran the formatter in --check mode and exited 0,
# because by then the worktree was already formatted. It checked the wrong
# thing. The state that matters is UNCOMMITTED, not UNFORMATTED.
# THE CHEAP L0 GATES BELONG IN THE PRE-FLIGHT TOO. `hooks/pre-push` runs them,
# correctly, and rejects at the END of a 545-second battery. Measured across
# 2026-08-31 they rejected FOUR of my pushes -- three for unpinned settled facts
# a lane had landed, once for a SLACK ratchet floor (achieved 1995, floor 1991,
# which lets the next regression to 1991 pass silently).
#
# Every rejection was correct. The cost was the battery, not the finding. These
# two run in well under a second combined, so there is no reason to learn about
# them nine minutes in.
if [ "${LANE_PUSH_SKIP_L0:-0}" != 1 ]; then
  for g in scripts/check-settled-fact-statements.py scripts/check-holdout-closed-evaluation.py; do
    [ -f "$g" ] || continue
    if ! out=$(python3 "$g" 2>&1); then
      echo "lane-push: DECLINING -- $g fails; the hook would reject this after the battery." >&2
      printf '%s\n' "$out" | tail -4 | sed 's/^/  /' >&2
      echo "  Fix it and re-push. LANE_PUSH_SKIP_L0=1 overrides." >&2
      exit 1
    fi
  done
fi

if [ "${LANE_PUSH_ALLOW_DIRTY:-0}" != 1 ]; then
  dirty=$(git status --porcelain --untracked-files=no)
  if [ -n "$dirty" ]; then
    echo "lane-push: DECLINING -- tracked files are modified and uncommitted." >&2
    printf '%s\n' "$dirty" | sed 's/^/  /' >&2
    echo "  hooks/pre-push refuses this too, but only after the full battery." >&2
    echo "  Commit or stash them first. LANE_PUSH_ALLOW_DIRTY=1 overrides." >&2
    exit 1
  fi
fi

[ "$DRY" = 1 ] && { echo "lane-push: --dry-run, not pushing"; exit 0; }

# The fast-forward check above cannot close the window it opens. The hook runs
# for MINUTES -- 176s to 545s here -- and the remote can advance inside it: on
# 2026-08-20 a push passed every gate and was then rejected with `cannot lock ref
# 'refs/heads/main': is at 4c7ad5e63 but expected 92fa6188a`. That is not a race
# you can win by checking harder beforehand, and paying the battery again by hand
# is the expensive way to lose it.
#
# `--retry N` re-merges the branch that moved and pushes again. It only ever
# merges the TARGET, and it stops on anything that is not a lock conflict, so a
# rejected push for a real reason (a failing gate) still fails immediately —
# which matters, because a failed gate and a rejected ref both exit 1 and their
# messages are hundreds of lines apart in the hook's output.
attempt=1
while :; do
  out=$(git push origin "HEAD:refs/heads/$target" 2>&1)
  status=$?
  printf '%s\n' "$out"
  [ "$status" -eq 0 ] && exit 0
  # One condition, several phrasings. GitHub says `cannot lock ref ... but
  # expected <sha>`; a local file remote says `incorrect old value provided`;
  # others say `stale info`, `fetch first`, or `non-fast-forward`. Matching only
  # the phrasing you happened to see in production leaves the control green while
  # the retry never fires -- which is how the fixture caught this.
  case "$out" in
    *"cannot lock ref"*|*"incorrect old value"*|*"stale info"*|*"fetch first"*|*"non-fast-forward"*) ;;
    *) exit "$status" ;;
  esac
  [ "$attempt" -ge "$RETRY" ] && exit "$status"
  attempt=$((attempt + 1))
  echo "lane-push: origin/$target moved during the hook; re-merging and retrying ($attempt/$RETRY)" >&2
  git fetch -q origin "$target" || exit "$status"
  if ! git merge --no-edit "origin/$target" >&2; then
    # PLAN.md conflicts on EVERY race, and resolving it by hand costs a second
    # full battery -- measured 2026-08-20 at 630-689 s each. It is a GENERATED
    # file (`scripts/gen-plan.py`, never hand-edited; the per-lane sources are
    # `docs/plan/status/<lane>.md`), so the resolution is always "regenerate",
    # and both lanes' rows survive because both status files do.
    #
    # Auto-resolve ONLY when it is the sole conflict. Any other conflicted path
    # is real content and still stops here: guessing at those is how lanes lose
    # each other's work.
    conflicted=$(git diff --name-only --diff-filter=U)
    if [ "$conflicted" = "PLAN.md" ] && [ -x scripts/gen-plan.py -o -f scripts/gen-plan.py ]; then
      echo "lane-push: PLAN.md is generated; regenerating instead of conflicting" >&2
      if python3 scripts/gen-plan.py >/dev/null 2>&1 \
         && [ "$(grep -c '<<<<<<<' PLAN.md)" -eq 0 ] \
         && git add -- PLAN.md && git commit --no-edit -q; then
        continue
      fi
    fi
    echo "lane-push: the re-merge conflicted; resolve it by hand." >&2
    printf '  %s\n' $conflicted >&2
    exit 1
  fi
done
