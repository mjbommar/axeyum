#!/usr/bin/env bash
# Mutation-kill verification for scripts/check-falsification-screen.py's
# guards (roadmap phase D3, ADR-0890).
#
# For every guard function, this GUTS the function body (in a SCRATCH COPY,
# never the shared checkout -- see CLAUDE.md's "MUTATION TESTING IN THE
# SHARED WORKTREE BREAKS OTHER LANES' BUILDS") to unconditionally
# `return []`, reruns scripts/tests/test_falsification_screen.py against the
# mutated copy, and reports which tests died. A guard is verified when
# EXACTLY ONE test dies -- more means the tests are not independent, fewer
# means nothing exercises that guard.
#
# Usage: bash scripts/tests/test-falsification-screen-mutation-verify.sh
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

mkdir -p "$SCRATCH/scripts/tests"
cp "$ROOT/scripts/tests/test_falsification_screen.py" "$SCRATCH/scripts/tests/test_falsification_screen.py"
cp "$ROOT/scripts/check-falsification-screen.py" "$SCRATCH/scripts/check-falsification-screen.py"
cp "$ROOT/scripts/falsification_screen_fixtures.py" "$SCRATCH/scripts/falsification_screen_fixtures.py"
cp "$ROOT/scripts/gen-falsification-screen.py" "$SCRATCH/scripts/gen-falsification-screen.py"
touch "$SCRATCH/scripts/__init__.py" "$SCRATCH/scripts/tests/__init__.py" 2>/dev/null || true
# ROOT in check-falsification-screen.py is computed as its own grandparent
# directory, so artifacts/falsification (receipts, dispatch log, pins) must
# exist under $SCRATCH too, or RealPackTests fails for a reason that has
# nothing to do with any guard -- copy them read-only, never mutated.
mkdir -p "$SCRATCH/artifacts"
cp -r "$ROOT/artifacts/falsification" "$SCRATCH/artifacts/falsification"
# check-falsification-screen.py also does `git merge-base` against its own
# ROOT for the real ordering test -- point it at the real repo via a git
# worktree-free trick: a .git FILE is not created here; instead this script
# copies the .git directory reference by running git from ROOT itself for
# that one test via a symlink, since is_ancestor_or_equal takes an explicit
# cwd default of ROOT (the scratch copy's own root). Symlink .git so git
# commands in the scratch tree resolve against the real repository.
ln -s "$ROOT/.git" "$SCRATCH/.git"

GUARDS="corpus_nonempty zero_executed_false false_statement_refuted definitions_nonempty zero_executed_definitions correct_matches_reference definition_has_mutation mutation_moves_observation review_obligations_present review_obligations_nonempty no_id_in_both_registries dispatch_has_receipt dispatch_receipt_is_clear dispatch_ordering receipt_ids_are_registered pin_drift pin_coverage"

baseline_out="$(cd "$SCRATCH" && python3 -m unittest scripts.tests.test_falsification_screen 2>&1 || true)"
baseline_fail="$(printf '%s' "$baseline_out" | grep -c '^FAIL:' || true)"
echo "baseline: $(printf '%s' "$baseline_out" | tail -1)"
if [ "$baseline_fail" != "0" ]; then
  echo "FATAL: baseline (unmutated) copy already has $baseline_fail failing test(s)"
  exit 1
fi

overall_bad=0
for g in $GUARDS; do
  work="$SCRATCH/work_$g"
  rm -rf "$work"
  mkdir -p "$work/scripts/tests"
  cp "$SCRATCH/scripts/check-falsification-screen.py" "$work/scripts/check-falsification-screen.py"
  cp "$SCRATCH/scripts/falsification_screen_fixtures.py" "$work/scripts/falsification_screen_fixtures.py"
  cp "$SCRATCH/scripts/gen-falsification-screen.py" "$work/scripts/gen-falsification-screen.py"
  cp "$SCRATCH/scripts/tests/test_falsification_screen.py" "$work/scripts/tests/test_falsification_screen.py"
  ln -sf "$ROOT/.git" "$work/.git"
  mkdir -p "$work/artifacts"
  cp -r "$SCRATCH/artifacts/falsification" "$work/artifacts/falsification"

  # Gut every function named `guard_<g>` (there may be several sharing a
  # prefix, e.g. pin_drift/pin_coverage map to guard_pin_drift and
  # guard_pin_coverage -- both start "def guard_pin_" for GUARDS entry
  # "pin_drift"/"pin_coverage" respectively, handled by exact prefix match).
  python3 - "$work/scripts/check-falsification-screen.py" "$g" <<'PYEOF'
import re
import sys

path, guard = sys.argv[1], sys.argv[2]
src = pathlib_text = open(path).read()
pattern = re.compile(
    r"(def guard_" + re.escape(guard) + r"\([^)]*\)[^:]*:\n)((?:    \"\"\".*?\"\"\"\n)?)",
    re.DOTALL,
)

def replace(m):
    return m.group(1) + m.group(2) + "    return []  # MUTATED: gutted for kill-verification\n"

new_src, n = pattern.subn(replace, src, count=1)
if n != 1:
    print(f"MUTATION-SITE-NOT-FOUND for guard_{guard}", file=sys.stderr)
    sys.exit(2)
open(path, "w").write(new_src)
PYEOF

  out="$(cd "$work" && python3 -m unittest scripts.tests.test_falsification_screen 2>&1 || true)"
  n_fail="$(printf '%s' "$out" | grep -c '^FAIL:' || true)"
  n_err="$(printf '%s' "$out" | grep -c '^ERROR:' || true)"
  total=$((n_fail + n_err))
  status="OK"
  if [ "$total" -eq 0 ]; then
    status="SURVIVED (0 tests died)"
    overall_bad=$((overall_bad + 1))
  elif [ "$total" -gt 1 ]; then
    status="TOO-WIDE ($total tests died)"
    overall_bad=$((overall_bad + 1))
  fi
  died="$(printf '%s' "$out" | grep -E '^(FAIL|ERROR):' | sed 's/^\(FAIL\|ERROR\): //' | tr '\n' ';' )"
  printf 'guard_%-32s died=%d  %-24s %s\n' "$g" "$total" "$status" "$died"
done

echo ""
if [ "$overall_bad" -eq 0 ]; then
  echo "ALL GUARDS VERIFIED: each mutation killed exactly one test"
  exit 0
else
  echo "$overall_bad guard(s) did not kill exactly one test -- see above"
  exit 1
fi
