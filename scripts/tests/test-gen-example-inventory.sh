#!/usr/bin/env bash
# Controls for `scripts/gen-example-inventory.py` (ADR-0539).
#
# The count it writes went stale eight times in one day before it existed, so the
# thing that matters is that `--check` FAILS on a stale marker and that the
# rewrite FIXES one. A generator shown only to agree with an already-correct file
# has been shown nothing.
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2

GEN=scripts/gen-example-inventory.py
FILES=(docs/documentation-plan.md docs/plan/global/30-workstream-state.md)
BACKUP=$(mktemp -d "${TMPDIR:-/tmp}/gen-example-inventory-XXXXXX")
restore() { for f in "${FILES[@]}"; do cp "$BACKUP/$(basename "$f")" "$f"; done; rm -rf "$BACKUP"; }
trap restore EXIT
for f in "${FILES[@]}"; do cp "$f" "$BACKUP/$(basename "$f")"; done

fail=0
check() { # name expected actual
  if [ "$2" = "$3" ]; then printf '  ok   %s\n' "$1"
  else printf '  FAIL %s: expected %s, got %s\n' "$1" "$2" "$3"; fail=1; fi
}

# 1. a clean tree passes
"$GEN" --check >/dev/null 2>&1; check "clean tree passes --check" 0 $?

# 2. a stale marker FAILS --check -- the control that matters
sed -i 's/all \([0-9]\+\) checked-in Cargo examples/all 999 checked-in Cargo examples/' \
  docs/documentation-plan.md
"$GEN" --check >/dev/null 2>&1; check "stale marker fails --check" 1 $?

# 3. ...and the failure NAMES the file, so a lane knows what to fix
out=$("$GEN" --check 2>&1)
case "$out" in *documentation-plan.md*) printf '  ok   the failure names the stale file\n';;
  *) printf '  FAIL the failure does not name the stale file\n'; fail=1;; esac

# 4. the rewrite repairs it, and --check then passes
"$GEN" >/dev/null 2>&1
"$GEN" --check >/dev/null 2>&1; check "rewrite repairs the marker" 0 $?

# 5. the repaired number is the tracked count, not 999 and not a guess
tracked=$(git ls-files 'crates/*/examples/*.rs' | wc -l | tr -d ' ')
grep -q "all ${tracked} checked-in Cargo examples" docs/documentation-plan.md
check "the repaired count equals the tracked file count ($tracked)" 0 $?

# 6. a missing marker is an ERROR (exit 2), not a silent pass
sed -i 's/all [0-9]\+ checked-in Cargo examples/all some Cargo examples/' docs/documentation-plan.md
"$GEN" --check >/dev/null 2>&1; check "a missing marker exits 2" 2 $?

[ "$fail" -eq 0 ] && echo "GEN_EXAMPLE_INVENTORY_CONTROLS|cases=6|failures=0" && exit 0
echo "GEN_EXAMPLE_INVENTORY_CONTROLS|failures>0"; exit 1
