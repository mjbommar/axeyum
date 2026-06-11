#!/usr/bin/env bash
# Verify that every relative markdown link in the repo's documentation
# resolves to an existing file. Used locally and by the docs-links CI job.
set -uo pipefail

cd "$(dirname "$0")/.."

fail=0

# Only repository-owned markdown: docs/, corpus/, crates/, the references
# index itself (not the gitignored clone contents), and root-level files.
files=$(find docs corpus crates -name '*.md' 2>/dev/null; ls references/README.md PLAN.md README.md CLAUDE.md CONTRIBUTING.md CHANGELOG.md 2>/dev/null)

for f in $files; do
  dir=$(dirname "$f")
  while IFS= read -r link; do
    # Skip absolute URLs and intra-page anchors.
    case "$link" in
      http://*|https://*|mailto:*) continue ;;
    esac
    target="${link%%#*}"
    [ -z "$target" ] && continue
    if [ ! -e "$dir/$target" ] && [ ! -e "$target" ]; then
      echo "BROKEN: $f -> $link"
      fail=1
    fi
  done < <(grep -oP '\]\(\K[^)]+' "$f" 2>/dev/null)
done

if [ "$fail" -eq 0 ]; then
  echo "all links ok"
fi
exit "$fail"
