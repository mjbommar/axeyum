#!/usr/bin/env bash
# Detect staged REVERTS of already-landed work in the shared index.
#
# This repository has lost work to the same mechanism seven times, and CLAUDE.md
# records the shape: you commit from a per-process index (`GIT_INDEX_FILE`), so
# `HEAD` advances, but the SHARED `.git/index` still holds the pre-commit blobs
# for those paths. Relative to the new `HEAD` that reads as a staged revert — and
# for a newly added file, a staged DELETION. The next lane to run a bare
# `git commit` applies it, and the work disappears inside a commit that looks
# like someone else's.
#
# It is invisible to the obvious checks. Every affected file is byte-identical to
# `HEAD` ON DISK, so `ls`, `git show` and reading the file all look correct; only
# the index is wrong. `git status` shows `MM`, which is easy to read as "someone
# is mid-edit" rather than "this is a loaded gun".
#
# Measured on 2026-08-17: six paths in that state, including 208 lines of the
# Euclid prime-divisor proof and a solver graph baseline with its script and
# tests — and ZERO genuinely staged edits, so the whole staged state was revert.
#
# Usage:
#   scripts/check-shared-index.sh          # report; exit 1 if any are found
#   scripts/check-shared-index.sh --fix    # clear them (a content no-op)
#
# `--fix` re-adds exactly the affected paths. That is safe precisely BECAUSE they
# are byte-identical to `HEAD`: re-adding changes no content and only replaces
# the stale blob. It deliberately does NOT `git read-tree HEAD`, which CLAUDE.md
# warns against — another lane may have legitimately staged work, and read-tree
# would drop it. Anything genuinely staged is reported and left alone.
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2

fix=0
[ "${1:-}" = "--fix" ] && fix=1

reverts=()
real=0

while read -r _status path; do
  [ -n "$path" ] || continue
  # A staged DELETION of a file that exists on disk is the same hazard.
  if [ -f "$path" ] && git show "HEAD:$path" 2>/dev/null | cmp -s - "$path"; then
    reverts+=("$path")
  else
    real=$((real + 1))
  fi
done < <(git diff --cached --name-status HEAD | awk '{print $1, $2}')

if [ "${#reverts[@]}" -eq 0 ]; then
  echo "shared-index: OK -- nothing staged that would revert landed work" \
       "($real genuinely staged path(s))"
  exit 0
fi

echo "shared-index: ${#reverts[@]} path(s) staged as a REVERT of landed work" \
     "($real genuinely staged path(s) left alone):" >&2
for path in "${reverts[@]}"; do
  echo "    $path" >&2
done

if [ "$fix" -eq 1 ]; then
  git add -- "${reverts[@]}" || exit 2
  echo "shared-index: cleared. Each file was byte-identical to HEAD, so no" \
       "content changed."
  exit 0
fi

echo "shared-index: every one of these is byte-identical to HEAD on disk, so" >&2
echo "  nothing is wrong with the files -- only the index. A bare \`git commit\`" >&2
echo "  by any lane would apply the revert. Run with --fix, or" >&2
echo "  \`git add --\` those paths yourself." >&2
exit 1
