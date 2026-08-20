#!/usr/bin/env bash
# The pre-push checkout must not inherit the caller worktree's GIT_DIR.
set -euo pipefail

here=$(cd "$(dirname "$0")/../.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

repo="$work/repo"
caller="$work/caller"
gate="$work/gate"
git -c init.defaultBranch=main init -q "$repo"
git -C "$repo" config user.email t@t
git -C "$repo" config user.name t
printf 'base\n' > "$repo/README.md"
git -C "$repo" add README.md
git -C "$repo" commit -qm base
base=$(git -C "$repo" rev-parse HEAD)
printf 'target\n' > "$repo/README.md"
printf 'fn target() {}\n' > "$repo/target.rs"
git -C "$repo" add README.md target.rs
git -C "$repo" commit -qm target
target=$(git -C "$repo" rev-parse HEAD)

git -C "$repo" worktree add -qb caller "$caller" "$base"
printf 'staged caller work\n' > "$caller/README.md"
git -C "$caller" add README.md
printf 'untracked caller work\n' > "$caller/WIP.md"

caller_gitdir=$(git -C "$caller" rev-parse --absolute-git-dir)
before_head=$(git -C "$caller" symbolic-ref HEAD)
before_index=$(git -C "$caller" diff --cached --binary)
before_status=$(git -C "$caller" status --porcelain=v1 --untracked-files=all)

# Simulate the environment Git supplies to hooks. Without clearing GIT_DIR,
# `git -C "$gate/worktree" checkout` rewrites caller_gitdir's HEAD/index while
# writing the target tree under the gate path.
prepared=$(
  cd "$caller"
  GIT_DIR="$caller_gitdir" \
    bash "$here/scripts/prepare-prepush-worktree.sh" "$repo" "$gate" "$target"
)

test "$prepared" = "$gate/worktree"
test "$(git -C "$prepared" rev-parse HEAD)" = "$target"
test -z "$(git -C "$prepared" status --porcelain=v1 --untracked-files=all)"
test "$(git -C "$caller" symbolic-ref HEAD)" = "$before_head"
test "$(git -C "$caller" diff --cached --binary)" = "$before_index"
test "$(git -C "$caller" status --porcelain=v1 --untracked-files=all)" = "$before_status"

# Reuse must remove both tracked dirt and ignored/untracked residue.
printf 'dirty\n' > "$prepared/README.md"
printf 'residue\n' > "$prepared/residue.tmp"
mkdir -p "$prepared/target"
printf 'ignored\n' > "$prepared/target/residue"
GIT_DIR="$caller_gitdir" \
  bash "$here/scripts/prepare-prepush-worktree.sh" "$repo" "$gate" "$target" >/dev/null
test -z "$(git -C "$prepared" status --porcelain=v1 --untracked-files=all)"
test ! -e "$prepared/residue.tmp"
test ! -e "$prepared/target/residue"
test "$(git -C "$caller" status --porcelain=v1 --untracked-files=all)" = "$before_status"

if bash "$here/scripts/prepare-prepush-worktree.sh" "$repo" / "$target" >/dev/null 2>&1; then
  echo "FAIL: unsafe gate root / was accepted" >&2
  exit 1
fi
if bash "$here/scripts/prepare-prepush-worktree.sh" "$repo" "$gate" deadbeef >/dev/null 2>&1; then
  echo "FAIL: nonexistent target was accepted" >&2
  exit 1
fi

echo "prepare-prepush-worktree: ok (foreign GIT_DIR isolated; exact clean target; caller preserved)"
