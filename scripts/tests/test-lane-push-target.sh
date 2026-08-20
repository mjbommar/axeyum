#!/usr/bin/env bash
# Control for `lane-push.sh --to`: the cost estimate must follow the ref being
# PUSHED, not the current branch's remote copy.
#
# The state under test is ordinary, not contrived: a session branch is pushed
# once, main moves on, the branch merges main down, and then a doc-only change
# is landed on main. Against the stale `origin/<branch>` the range re-counts
# every `.rs` merged down in between, and the script reports a FULL BATTERY for
# a push the hook will exit immediately on.
#
# This is a control, so it asserts BOTH readings. Asserting only that `--to main`
# says FREE would pass against a script that always says FREE.
set -uo pipefail
here=$(cd "$(dirname "$0")/../.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# The bare remote must live OUTSIDE the worktree; inside, git tracks its refs as
# files and `git checkout` then refuses to switch branches.
git -c init.defaultBranch=main init -q --bare "$work/origin.git"
mkdir -p "$work/wt" && cd "$work/wt" || exit 2
git -c init.defaultBranch=main init -q .
git config user.email t@t && git config user.name t
git remote add origin ../origin.git
echo hi > README.md && git add -A && git commit -qm base && git push -q origin main
git checkout -qb feature && git push -q origin feature          # upstream pinned here
git checkout -q main && echo 'fn a(){}' > a.rs && git add -A \
  && git commit -qm rust && git push -q origin main
git checkout -q feature && git merge -q main -m merge \
  && echo doc > d.md && git add -A && git commit -qm doconly
git fetch -q origin

fail=0
stale=$(bash "$here/scripts/lane-push.sh" --dry-run 2>&1)
targeted=$(bash "$here/scripts/lane-push.sh" --to main --dry-run 2>&1)

case "$stale" in
  *"FULL BATTERY"*) ;;
  *) echo "FAIL: without --to, expected the stale-upstream overcount (FULL BATTERY):"
     echo "$stale" | sed 's/^/    /'; fail=1 ;;
esac
case "$targeted" in
  *FREE*) ;;
  *) echo "FAIL: with --to main, the range holds no .rs and the estimate must be FREE:"
     echo "$targeted" | sed 's/^/    /'; fail=1 ;;
esac

# And a push that could not land must be refused BEFORE the hook is paid for.
git checkout -q main && echo more >> README.md && git add -A \
  && git commit -qm ahead && git push -q origin main
git checkout -q feature
behind=$(bash "$here/scripts/lane-push.sh" --to main --dry-run 2>&1); rc=$?
if [ "$rc" -eq 0 ]; then
  echo "FAIL: origin/main is not an ancestor of HEAD; --to main must decline, got rc=0:"
  echo "$behind" | sed 's/^/    /'; fail=1
fi

[ "$fail" = 0 ] && echo "lane-push --to: ok (estimate follows the pushed ref; non-ff declined)"
exit "$fail"
