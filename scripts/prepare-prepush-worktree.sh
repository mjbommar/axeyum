#!/usr/bin/env bash
# Prepare the persistent pre-push checkout without touching the caller's Git
# metadata. Git deliberately exports GIT_DIR and related variables to hooks;
# `git -C <other-worktree>` does not override them.
set -euo pipefail

if [ "$#" -ne 3 ]; then
  echo "usage: $0 <repo-root> <gate-root> <target-sha>" >&2
  exit 2
fi

repo_root="$1"
gate_root="$2"
target_sha="$3"

case "$gate_root" in
  ""|/) echo "prepare-prepush-worktree: unsafe gate root: ${gate_root:-<empty>}" >&2; exit 2 ;;
esac

# This list must be obtained before clearing the variables: in a hook, the
# inherited GIT_DIR is what tells `git rev-parse` which local variables Git set.
mapfile -t local_git_env < <(git rev-parse --local-env-vars)
unset "${local_git_env[@]}"

repo_root="$(git -C "$repo_root" rev-parse --show-toplevel)"
target_sha="$(git -C "$repo_root" rev-parse --verify "${target_sha}^{commit}")"
mkdir -p "$gate_root"
gate_worktree="$gate_root/worktree"

if ! { git -C "$gate_worktree" rev-parse --git-dir >/dev/null 2>&1 \
       && git -C "$gate_worktree" checkout --detach --force --quiet "$target_sha"; }; then
  # The path is exact and validated above; never accept a caller-supplied
  # worktree path independently of the dedicated gate root.
  if [ -e "$gate_worktree" ]; then
    rm -rf -- "$gate_worktree"
  fi
  git -C "$repo_root" worktree prune
  git -C "$repo_root" worktree add --detach --quiet "$gate_worktree" "$target_sha"
fi
git -C "$gate_worktree" clean -xdfq

actual_sha="$(git -C "$gate_worktree" rev-parse HEAD)"
if [ "$actual_sha" != "$target_sha" ]; then
  echo "prepare-prepush-worktree: HEAD mismatch: expected $target_sha, got $actual_sha" >&2
  exit 1
fi
if [ -n "$(git -C "$gate_worktree" status --porcelain=v1 --untracked-files=all)" ]; then
  echo "prepare-prepush-worktree: prepared checkout is not clean" >&2
  git -C "$gate_worktree" status --short >&2
  exit 1
fi

printf '%s\n' "$gate_worktree"
