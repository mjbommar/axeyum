#!/usr/bin/env bash
# Emit a well-formed docs/plan/status/<n>-<lane>.md skeleton.
#
# WHY THIS EXISTS. `docs/plan/status/README.md` documents the two rules a status
# file must satisfy -- every line must sit under a `<!-- plan-section: ... -->`
# marker, and `landed-changes` takes DATA ROWS ONLY, no table header. Both rules
# were documented before 2026-08-27 and SIX lanes broke them that day in three
# distinct shapes: no markers at all (four lanes), text before the first marker,
# and a `| date | change | notes |` header row where the generator wants data.
#
# Each failure blocks `PLAN.md` regeneration entirely, and it surfaces at the
# coordinator rather than at the lane that wrote the file -- so the lane never
# sees its own mistake. Prose did not fix this; a skeleton that is correct by
# construction might.
#
# Usage:  scripts/new-lane-status.sh 162 my-lane > docs/plan/status/162-my-lane.md
#     or: scripts/new-lane-status.sh 162 my-lane --write
set -euo pipefail

if [ $# -lt 2 ]; then
  echo "usage: $0 <number> <lane-name> [--write]" >&2
  exit 2
fi

n="$1"; lane="$2"; write="${3:-}"
today="$(date +%Y-%m-%d)"

body=$(cat <<EOF
# Lane: ${lane} — one line saying what this lane is for

<!-- plan-section: lane-status -->

**Your lane's block (\`WIP\`, ${lane}, ${today}).** What landed, what did not,
and what the next lane needs to know. State a negative as precisely as a
positive — a sized negative is a complete deliverable here.

<!-- plan-section: landed-changes -->

| ${today} | ${lane} | what landed, in one line |
EOF
)

if [ "$write" = "--write" ]; then
  out="docs/plan/status/${n}-${lane}.md"
  if [ -e "$out" ]; then echo "refusing: $out exists" >&2; exit 1; fi
  printf '%s\n' "$body" > "$out"
  echo "wrote $out"
else
  printf '%s\n' "$body"
fi
