#!/usr/bin/env bash
# Scope-aware iteration gate.
#
# Runs ONLY the gates relevant to what changed vs a base ref (default: `main`),
# instead of the full `just check` (13 gates over the whole workspace, tens of
# minutes, plus a ~40-min GitHub CI). `just check` remains the authoritative
# pre-merge/CI gate; use THIS while iterating so feedback is proportional to the
# change. It deliberately UNDER-promises: any changed path it can't confidently
# map to a scoped gate is reported so you know to fall back to `just check`.
#
# Usage:  scripts/check-scope.sh [base-ref]      (default base-ref: main)
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
BASE="${1:-main}"

# Union of: committed diff vs base, unstaged working changes, and new files.
changed=$( { git diff --name-only "$BASE"...HEAD 2>/dev/null
             git diff --name-only 2>/dev/null
             git ls-files --others --exclude-standard 2>/dev/null
           } | sort -u | grep -v '^[[:space:]]*$' || true )

if [ -z "$changed" ]; then
  echo "check-scope: no changes vs $BASE — nothing to gate."
  exit 0
fi

echo "check-scope: changed vs $BASE:"; echo "$changed" | sed 's/^/  /'; echo

rust=$(echo "$changed"   | grep -E '^crates/[^/]+/' || true)
crates=$(echo "$rust"    | grep -oE '^crates/[^/]+' | sort -u || true)
py=$(echo "$changed"     | grep -E '^scripts/.*\.py$' || true)
unmapped=$(echo "$changed" | grep -vE '^crates/|^scripts/.*\.py$|^docs/|\.md$' || true)

rc=0
run() { echo "+ $*"; "$@" || rc=1; echo; }

# ---- Rust crates: test + clippy only the touched packages ----
if [ -n "$crates" ]; then
  pkgs=(); for c in $crates; do pkgs+=(-p "${c#crates/}"); done
  # axeyum-cas: skip the order-255 moment proofs unless moment code changed.
  skip=()
  if echo "$crates" | grep -qx 'crates/axeyum-cas' \
     && ! echo "$rust" | grep -qiE 'moment|squared_binomial|falling_factorial'; then
    skip=(-- --skip squared_binomial_moment_family_is_checked \
             --skip squared_binomial_falling_moment_family_is_checked)
    echo "check-scope: axeyum-cas touched but not moment code — skipping the ~15-min moment proofs."
  fi
  run cargo test "${pkgs[@]}" --lib "${skip[@]}"
  run cargo clippy "${pkgs[@]}" --all-targets -- -D warnings
fi

# ---- Python (scripts/*.py): touched test modules + the owning lane gate ----
if [ -n "$py" ]; then
  tests=$(echo "$py" | grep -E '/tests/test_.*\.py$' || true)
  [ -n "$tests" ] && run python3 -m pytest $tests -q
  echo "$py" | grep -qE 'lean_|/lean'      && run python3 -m unittest scripts.tests.test_lean_complete_parity
  echo "$py" | grep -qE 'smtcomp_repro|smtcomp' && run bash scripts/check-smtcomp-resume.sh
fi

# ---- Honesty: anything outside the mapped scopes needs the full gate ----
if [ -n "$unmapped" ]; then
  echo "check-scope: NOTE — these paths are outside the scoped map; run full 'just check' before merge:"
  echo "$unmapped" | sed 's/^/  /'; echo
fi

if [ "$rc" -eq 0 ]; then
  echo "check-scope: scoped gates PASSED. Run full 'just check' (or 'just test-guarded') once before you push."
else
  echo "check-scope: FAILURES above."
fi
exit "$rc"
