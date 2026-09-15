#!/usr/bin/env bash
# Re-pin ADR-1966's refusal-propagation baseline after ADR-2100, and prove the
# ratchet still fires afterwards.
#
# WHY RE-PIN AT ALL. The baseline is a living pin, not a measurement: ADR-1966
# committed it "so a NEW site of this shape fails rather than waiting to be
# found by accident a fifth time". ADR-2100 restructures the ladder's error
# channel, so two entries change spelling and five drop out. Leaving the old
# pin in place would make the ratchet fire unconditionally, and **a gate that
# "fails" unconditionally looks exactly like a working one until you check that
# it also passes when it should** -- which is the inverted control ADR-1966's
# own lane caught in itself.
#
# WHAT MUST BE TRUE AFTER. The ratchet has to still FIRE on a re-introduced
# site. This script checks both directions, in a scratch copy, and refuses to
# report success on either half alone.
#
# Usage: repin-ratchet.sh [--write]
set -u
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BASE="$ROOT/bench-results/dispatch-decline-audit-20260913/refusal-propagation-baseline.json"
ENUM="$ROOT/scripts/enumerate-dispatch-refusal-propagation.py"
SRC="$ROOT/crates/axeyum-solver/src"

[ -f "$BASE" ] || { echo "ABORT: no baseline at $BASE"; exit 2; }
[ -f "$ENUM" ] || { echo "ABORT: no enumerator at $ENUM"; exit 2; }

TMP=$(mktemp -d -p "${TMPDIR:-/tmp}" repin-XXXXXX)
trap 'rm -rf "$TMP"' EXIT

echo "--- the delta against the pinned baseline ---"
python3 "$ENUM" --root "$SRC" --quiet --json "$TMP/new.json" --fail-on-new "$BASE"
echo "ratchet-on-current-tree-exit=$?"

python3 - "$BASE" "$TMP/new.json" <<'PY'
import json, sys
old = json.load(open(sys.argv[1]))
new = json.load(open(sys.argv[2]))


def key(s):
    return (s["path"], s["fn"], s["kind"], s["callee"])


o = {key(s) for s in old["sites"]}
n = {key(s) for s in new["sites"]}
print(f"pinned sites: {len(o)}   current sites: {len(n)}")
print(f"\nGONE from the pin ({len(o - n)}):")
for s in sorted(o - n):
    print("  ", s)
print(f"\nNEW since the pin ({len(n - o)}):")
for s in sorted(n - o):
    print("  ", s)
PY

if [ "${1:-}" != "--write" ]; then
  echo
  echo "(dry run -- pass --write to update the pin)"
  exit 0
fi

cp "$TMP/new.json" "$BASE"
echo
echo "--- the ratchet on the RE-PINNED tree (must be 0) ---"
python3 "$ENUM" --root "$SRC" --quiet --fail-on-new "$BASE"
clean=$?
echo "clean-exit=$clean"

echo "--- the ratchet on a tree with ONE site re-introduced (must be non-zero) ---"
cp -r "$SRC" "$TMP/src"
python3 - "$TMP/src/auto.rs" <<'PY'
import sys
p = sys.argv[1]
s = open(p).read()
# Re-introduce the ADR-2100 shape at the `lira-dpll` rung: replace the funnel
# with a bare `?`, which is the exact defect this whole family is about.
old = """        match check_with_arith_dpll(arena, assertions, config) {"""
assert s.count(old) == 1, f"anchor matched {s.count(old)} times -- find it, do not guess"
new = """        let _reintroduced = check_with_arith_dpll(arena, assertions, config)?;
        match check_with_arith_dpll(arena, assertions, config) {"""
open(p, "w").write(s.replace(old, new, 1))
print("re-introduced one bare-`?` propagation site at the lira-dpll rung")
PY
python3 "$ENUM" --root "$TMP/src" --quiet --fail-on-new "$BASE"
mutated=$?
echo "mutated-exit=$mutated"

[ "$clean" -eq 0 ] || { echo "RE-PIN FAILED: the ratchet still fires on the clean tree"; exit 1; }
[ "$mutated" -ne 0 ] || { echo "RATCHET IS VACUOUS -- it did not fire on a re-introduced site"; exit 1; }
echo "REPIN-OK: clean tree passes, a re-introduced site fails"
