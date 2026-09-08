#!/usr/bin/env bash
# Positive control for the config-registry staleness check (ADR-1762).
#
# `check-config-registry-staleness.py` normally exits 0, and exit 0 is exactly
# what a checker that CANNOT FIRE prints. Two of the three defects found in that
# script during its own development were of precisely that kind: a regex missing
# `re.MULTILINE` that made the parser return zero entries, and a `sym(...)`
# pattern that did not survive rustfmt's trailing comma so every dated entry
# parsed with an EMPTY `rests_on`. Both printed "no dated justification is
# stale" for all 24 dated entries, indistinguishable from a clean bill of health.
#
# So the check ships with a control, and this runs it:
#
#   1. the in-tree registry must exit 0            (no genuinely stale entry)
#   2. a copy with `MAX_ONLINE_LRA_ATOMS` dated 2026-08-03 -- its REAL original
#      date -- must exit 1 and name `MAX_LRA_CACHED_COEFFICIENTS`
#      (the check can fire, on the exact failure it was built for)
#   3. that same copy with the entry's `rests_on` EMPTIED must exit 0 again
#      (the dependency is load-bearing, not decoration)
#
# Step 3 is the mutation test on our own gate. Without it, step 2 could be
# passing because of the entry's self-dependency alone, and the cross-file
# dependency -- the whole point of the staleness contract -- would be untested.
#
# Nothing here writes to the repository: the copies live in a throwaway
# directory. Usage: scripts/tests/test-config-registry-staleness-control.sh
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CHECK="$ROOT/scripts/check-config-registry-staleness.py"
REGISTRY="$ROOT/crates/axeyum-solver/src/config_registry.rs"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/axeyum-config-staleness-control.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

fails=0
step() { printf '\n== %s\n' "$1"; }
ok()   { printf '   PASS: %s\n' "$1"; }
bad()  { printf '   FAIL: %s\n' "$1"; fails=$((fails + 1)); }

for f in "$CHECK" "$REGISTRY"; do
  if [ ! -f "$f" ]; then
    printf 'FAIL: missing %s\n' "$f"
    exit 2
  fi
done

# ---------------------------------------------------------------------------
step "1. the in-tree registry has no genuinely stale dated justification"
python3 "$CHECK" >"$WORK/real.out" 2>&1
real_rc=$?
if [ "$real_rc" -eq 0 ]; then
  ok "exit 0"
else
  bad "expected exit 0, got $real_rc"
  sed 's/^/     /' "$WORK/real.out"
fi

# ---------------------------------------------------------------------------
step "2. backdating MAX_ONLINE_LRA_ATOMS to 2026-08-03 must be caught"
python3 - "$REGISTRY" "$WORK/backdated.rs" <<'PY'
import sys
src = open(sys.argv[1], encoding="utf-8").read()
old = '"ADR-1752",\n            "2026-09-07",\n            Some("e62086742"),'
new = '"ADR-1752",\n            "2026-08-03",\n            Some("e62086742"),'
if old not in src:
    sys.exit("control could not be built: the MAX_ONLINE_LRA_ATOMS "
             "justification no longer has the shape this control edits")
open(sys.argv[2], "w", encoding="utf-8").write(src.replace(old, new, 1))
PY
if [ $? -ne 0 ]; then
  bad "could not build the backdated control"
else
  python3 "$CHECK" --registry "$WORK/backdated.rs" >"$WORK/back.out" 2>&1
  back_rc=$?
  if [ "$back_rc" -eq 1 ]; then
    ok "exit 1"
  else
    bad "expected exit 1, got $back_rc"
  fi
  # It must fire for the RIGHT reason: the cross-file dependency, not merely
  # the entry's own definition site.
  if grep -q 'MAX_LRA_CACHED_COEFFICIENTS' "$WORK/back.out"; then
    ok "names lra_online.rs::MAX_LRA_CACHED_COEFFICIENTS"
  else
    bad "fired without naming the cross-file dependency it was built for"
    sed 's/^/     /' "$WORK/back.out"
  fi
  if grep -q '96ff85930' "$WORK/back.out"; then
    ok "names 96ff85930, the 2026-08-06 commit that falsified the measurement"
  else
    bad "did not name the commit that falsified the measurement"
  fi
fi

# ---------------------------------------------------------------------------
step "3. with the dependency removed the same backdated entry passes again"
python3 - "$WORK/backdated.rs" "$WORK/nodep.rs" <<'PY'
import re, sys
src = open(sys.argv[1], encoding="utf-8").read()
# Empty the `rests_on` list of the MAX_ONLINE_LRA_ATOMS entry only.
m = re.search(
    r'(    ConfigEntry \{\n        name: "MAX_ONLINE_LRA_ATOMS",\n.*?'
    r'Some\("e62086742"\),\n)(\s*&\[.*?\n\s*\],\n)',
    src, re.S)
if not m:
    sys.exit("control could not be built: the rests_on list no longer has "
             "the shape this control edits")
src = src[:m.start(2)] + "            &[],\n" + src[m.end(2):]
open(sys.argv[2], "w", encoding="utf-8").write(src)
PY
if [ $? -ne 0 ]; then
  bad "could not build the dependency-removed mutant"
else
  python3 "$CHECK" --registry "$WORK/nodep.rs" >"$WORK/nodep.out" 2>&1
  nodep_rc=$?
  if [ "$nodep_rc" -eq 0 ]; then
    ok "exit 0 — the dependency is what makes step 2 fire, not the date alone"
  else
    bad "expected exit 0 with no dependencies, got $nodep_rc"
    sed 's/^/     /' "$WORK/nodep.out"
  fi
fi

printf '\n'
if [ "$fails" -eq 0 ]; then
  echo "CONFIG_STALENESS_CONTROL|PASSED"
  exit 0
fi
echo "CONFIG_STALENESS_CONTROL|FAILED|checks_failed=$fails"
exit 1
