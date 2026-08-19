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
#   scripts/lane-push.sh --dry-run    # report only
#   scripts/lane-push.sh --force      # push even if another push is running
#
# Exit 75 (EX_TEMPFAIL) when it declines because another push holds the lock --
# distinguishable from a rejected push, which is the point.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)" || exit 2

DRY=0; FORCE=0
for a in "$@"; do case "$a" in
  --dry-run) DRY=1 ;;
  --force) FORCE=1 ;;
  *) echo "lane-push: unknown option $a" >&2; exit 2 ;;
esac; done

branch=$(git rev-parse --abbrev-ref HEAD)
upstream="origin/$branch"
if ! git rev-parse --verify -q "$upstream" >/dev/null; then
  echo "lane-push: no $upstream yet; pushing will create it"
  range="HEAD"
else
  range="$upstream..HEAD"
fi

n=$(git rev-list --count "$range" 2>/dev/null || echo 0)
if [ "$n" = 0 ]; then
  echo "lane-push: nothing to push ($branch is up to date with $upstream)"
  exit 0
fi

# What the hook will decide, computed the same way it does.
base=$(git rev-parse "${upstream}" 2>/dev/null || git merge-base origin/main HEAD)
changed=$(git diff --name-only "$base" HEAD -- '*.rs' '*.toml' | wc -l)
if [ "$changed" -eq 0 ]; then
  cost="FREE — no *.rs/*.toml in the range, the hook exits before any cargo step"
else
  cost="FULL BATTERY — $changed Rust/TOML file(s) changed; 545 s uncontended, far more under lane contention"
fi
echo "lane-push: $n commit(s) on $branch"
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

[ "$DRY" = 1 ] && { echo "lane-push: --dry-run, not pushing"; exit 0; }
exec git push origin HEAD
