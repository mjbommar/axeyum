#!/usr/bin/env bash
# Demonstrate that `check-absence-claims.py` goes RED on the seeded claims.
#
# The four seeded records in this repository carry `was-absent:` markers,
# because the obstacles they describe have cleared. This script copies those
# files into a scratch root, rewrites `was-absent:` to `absent:` -- restoring
# each document to the state it was actually in on the day it was written --
# and requires the gate to FAIL naming every declaration.
#
# That is the non-vacuity demonstration: the gate is green on the tree as it
# stands, and the ONLY difference in the red run is the one word that turns a
# historical record back into a live claim.
#
# It never mutates a tracked file: everything happens under a scratch root
# (CLAUDE.md forbids in-place mutation in the shared checkout -- another lane
# compiles from that file and the failure looks like their bug).
#
# Usage: scripts/tests/demo-absence-expiry-seeds.sh <projection.tsv>
# Exit 0 when the gate behaved as required in BOTH directions.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
PROJECTION="${1:?usage: $0 <kernel_declaration_projection stdout>}"

SEEDS=(
  "docs/mathematics-2026-08/diary-exact-root-obstruction.md"
  "docs/research/11-design-review/2026-08-27-rat-reindexing-and-the-denominator-gap.md"
  "CLAUDE.md"
)
# Every declaration the seeds name. The red run must name each one.
EXPECTED=(
  "CReal.strict_mono_magnitude"
  "CReal.diff_le_of_strict_mono_magnitude"
  "CReal.converges_comp_eventually"
  "Rat.sumRange_diagonal"
  "Rat.sumRange_rect_eq_diag_add_corner"
  "Complex.sumRange_mul_eq_diag_add_corner"
  "CReal.weierstrassMTest"
  "CReal.close_within_of_within"
)

WORK="$(mktemp -d "${TMPDIR:-/tmp}/absence-expiry-demo.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

for seed in "${SEEDS[@]}"; do
  mkdir -p "$WORK/$(dirname "$seed")"
  cp "$ROOT/$seed" "$WORK/$seed"
  # The one-word difference between a historical record and a live claim.
  sed -i 's/<!-- was-absent:/<!-- absent:/g' "$WORK/$seed"
done

cat > "$WORK/census.json" <<'JSON'
{
  "authority_declaration_floor": 1750,
  "bare_named_claim_budget": 9999,
  "excluded_paths": []
}
JSON

set +e
OUT="$(python3 "$ROOT/scripts/check-absence-claims.py" \
  --root "$WORK" --census "$WORK/census.json" \
  --projection-file "$PROJECTION" 2>&1)"
STATUS=$?
set -e

printf '%s\n' "$OUT"

if [ "$STATUS" -eq 0 ]; then
  echo "DEMO FAILED: the gate exited 0 on live claims about declarations that exist." >&2
  exit 1
fi
if [ "$STATUS" -ne 1 ]; then
  echo "DEMO FAILED: expected exit 1 (a finding); got $STATUS (a broken gate)." >&2
  exit 1
fi

missing=0
for name in "${EXPECTED[@]}"; do
  # `grep -c` consumes the whole input and cannot SIGPIPE (CLAUDE.md bans
  # `grep -q` as a pipeline consumer); the count is what is tested.
  hits="$(printf '%s\n' "$OUT" | /usr/bin/grep -cF "EXPIRED  " | cat)"
  named="$(printf '%s\n' "$OUT" | /usr/bin/grep -F "EXPIRED  " | /usr/bin/grep -cF "$name" || true)"
  if [ "$named" -eq 0 ]; then
    echo "DEMO FAILED: the red run did not report $name as EXPIRED." >&2
    missing=1
  fi
  : "$hits"
done
[ "$missing" -eq 0 ] || exit 1

# The green control, on the same files WITHOUT the one-word rewrite. Without
# this half, "the gate went red" says nothing -- a gate that always reds is
# the same as one that never does.
for seed in "${SEEDS[@]}"; do
  cp "$ROOT/$seed" "$WORK/$seed"
done
set +e
GREEN="$(python3 "$ROOT/scripts/check-absence-claims.py" \
  --root "$WORK" --census "$WORK/census.json" \
  --projection-file "$PROJECTION" 2>&1)"
GSTATUS=$?
set -e
printf '%s\n' "$GREEN"
if [ "$GSTATUS" -ne 0 ]; then
  echo "DEMO FAILED: the green control did not pass (exit $GSTATUS)." >&2
  exit 1
fi

echo "DEMO OK: ${#EXPECTED[@]} seeded claim(s) red as live claims, green as historical records."
