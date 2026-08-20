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

# --retry must recover when the target moves DURING the push, and must not retry
# a rejection for any other reason.
#
# The race is simulated by moving the remote ref from inside the pre-push hook —
# which is exactly where the real one happens, since the real hook runs for
# minutes. Plumbing (`update-ref` on the bare repo) rather than a nested clone:
# a nested push re-enters the hook and the fixture hangs.
git checkout -q main && git reset -q --hard origin/main
echo other >> README.md && git add -A && git commit -qm "other lane's commit"
OTHER=$(git rev-parse HEAD)
# The bare repo must actually HAVE the object before a ref can point at it.
git push -q origin "HEAD:refs/heads/scratch"
git reset -q --hard origin/main
git checkout -q feature
# The non-fast-forward block above deliberately left origin/main ahead; sync so
# the pre-push decline is not what this case measures.
git merge -q --no-edit origin/main -m sync

cat > "$work/wt/.git/hooks/pre-push" <<HOOK
#!/usr/bin/env bash
# Once: move the remote's main out from under this push.
if [ ! -e "$work/raced" ]; then
  : > "$work/raced"
  git --git-dir="$work/origin.git" update-ref refs/heads/main $OTHER
fi
exit 0
HOOK
chmod +x "$work/wt/.git/hooks/pre-push"

out=$(bash "$here/scripts/lane-push.sh" --to main --retry 3 2>&1); rc=$?
rm -f "$work/wt/.git/hooks/pre-push"
if [ "$rc" -ne 0 ]; then
  echo "FAIL: --retry did not recover from a mid-push remote advance (rc=$rc):" >&2
  echo "$out" | tail -8 | sed 's/^/    /' >&2; fail=1
elif ! printf '%s' "$out" | grep -q "moved during the hook"; then
  echo "FAIL: the push succeeded without the race firing; the fixture proved nothing." >&2
  echo "$out" | tail -6 | sed 's/^/    /' >&2; fail=1
else
  echo "  ok   --retry re-merged and landed after a mid-push race"
fi

# ...and the other lane's commit must still be there: a retry that discards it
# would be worse than a failed push.
git fetch -q origin main
if git merge-base --is-ancestor "$OTHER" origin/main; then
  echo "  ok   the retry preserved the commit that raced in"
else
  echo "FAIL: the retry dropped the other lane's commit" >&2; fail=1
fi

[ "$fail" = 0 ] && echo "lane-push --to: ok (estimate follows the pushed ref; non-ff declined; --retry recovers)"
exit "$fail"
