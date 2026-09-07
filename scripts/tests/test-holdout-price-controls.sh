#!/usr/bin/env bash
#
# Control suite for `scripts/price-holdout-family.py`.
#
# Same discipline as `test-producer-channel-controls.sh`: one control per guard,
# each asserting on that guard's OWN finding text, and a `--guard-deletion` mode
# that deletes each `# GUARD:<id>` group and requires EXACTLY ONE control to die.
#
# The mutants here work on COPIES of the autogenesis manifests in a scratch root.
# Nothing writes to `artifacts/autogenesis/`, and no held-out id is printed by
# this suite or by anything it runs -- the `id-leak` control checks that the
# priced script cannot start printing them.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRIPT="$ROOT/scripts/price-holdout-family.py"
AUTOGEN="$ROOT/artifacts/autogenesis"

SCRATCH="$(mktemp -d "${TMPDIR:-/tmp}/holdout-price-controls.XXXXXX")"
trap 'rm -rf "$SCRATCH"' EXIT

PASS=0
FAIL=0
DIED=()

expect_finding() {
  local name="$1" script="$2" autogen="$3" needle="$4" rc
  AXEYUM_HOLDOUT_PRICE_AUTOGEN="$autogen" \
  AXEYUM_HOLDOUT_PRICE_GATE="${GATE_OVERRIDE:-$ROOT/scripts/check-autogenesis-holdout-isolation.py}" \
    python3 "$script" --check >"$SCRATCH/out" 2>&1
  rc=$?
  if [ "$rc" -ne 0 ] && grep -F -- "$needle" "$SCRATCH/out" >/dev/null; then
    [ "${QUIET:-0}" = 1 ] || echo "  PASS  $name"
    PASS=$((PASS + 1))
  else
    [ "${QUIET:-0}" = 1 ] || echo "  FAIL  $name  (exit=$rc, needle not found: $needle)"
    FAIL=$((FAIL + 1))
    DIED+=("$name")
  fi
}

build_inputs() {
  # A1 -> GUARD:empty-population.  Every held-out row reassigned: the blind
  # population is gone and the price is about nothing.
  mkdir -p "$SCRATCH/a1"
  cp "$AUTOGEN"/nursery-v1.json "$AUTOGEN"/nursery-v2-extension.json \
     "$AUTOGEN"/mathlib-nursery-split-policy-v1.json "$SCRATCH/a1/"
  python3 - "$SCRATCH/a1" <<'PY'
import sys, json, pathlib
for name in ("nursery-v1.json", "nursery-v2-extension.json"):
    p = pathlib.Path(sys.argv[1]) / name
    d = json.loads(p.read_text())
    for key in ("entries", "facts", "rows"):
        for e in d.get(key, []) or []:
            if isinstance(e, dict) and e.get("partition") == "held-out":
                e["partition"] = "development"
    p.write_text(json.dumps(d))
PY

  # A2 -> GUARD:population-mismatch.  One held-out row removed from the copy the
  # price reads, while the enforcing gate still protects the real manifests.
  mkdir -p "$SCRATCH/a2"
  cp "$AUTOGEN"/nursery-v1.json "$AUTOGEN"/nursery-v2-extension.json \
     "$AUTOGEN"/mathlib-nursery-split-policy-v1.json "$SCRATCH/a2/"
  python3 - "$SCRATCH/a2" <<'PY'
import sys, json, pathlib
p = pathlib.Path(sys.argv[1]) / "nursery-v1.json"
d = json.loads(p.read_text())
done = False
for key in ("entries", "facts", "rows"):
    for e in d.get(key, []) or []:
        if not done and isinstance(e, dict) and e.get("partition") == "held-out":
            e["partition"] = "development"
            done = True
p.write_text(json.dumps(d))
PY

  # A3 -> GUARD:recycled-family.  An amended (spent) family put back into the
  # blind population -- what ADR-0542 made a generator error.
  mkdir -p "$SCRATCH/a3"
  cp "$AUTOGEN"/nursery-v1.json "$AUTOGEN"/nursery-v2-extension.json \
     "$AUTOGEN"/mathlib-nursery-split-policy-v1.json "$SCRATCH/a3/"
  python3 - "$SCRATCH/a3" <<'PY'
import sys, json, pathlib
root = pathlib.Path(sys.argv[1])
pol = json.loads((root / "mathlib-nursery-split-policy-v1.json").read_text())
spent = {a["family"] for a in pol.get("amendments", []) if a.get("from") == "held-out"}
for name in ("nursery-v1.json", "nursery-v2-extension.json"):
    p = root / name
    d = json.loads(p.read_text())
    for key in ("entries", "facts", "rows"):
        for e in d.get(key, []) or []:
            if isinstance(e, dict) and e.get("family") in spent:
                e["partition"] = "held-out"
    p.write_text(json.dumps(d))
PY

  # A4 -> GUARD:empty-family has NO control and no mutant. In this derivation a
  # family exists only by having a held-out row, so a zero-row held-out family is
  # not constructible from the manifests. The guard stays because a future
  # derivation that reads families from a declaration list COULD produce one; it
  # is reported UNTESTED in the guard-deletion table rather than left implied.
}

# A5 -> GUARD:id-leak is a script mutant; A6 -> GUARD:gate-unavailable is an
# input redirection.
build_mutants() {
  local src="${1:-$SCRIPT}"
  # A5: the family listing starts printing row ids instead of counting them.
  python3 - "$src" "$SCRATCH/a5.py" <<'PY'
import sys
t = open(sys.argv[1]).read()
old = '    for fam, size in sorted(sizes.items()):\n        out(f"    {size:4d}  {fam}")'
new = '    for fam, size in sorted(sizes.items()):\n        out(f"    {size:4d}  {fam}  {rows[fam][0]}")'
assert old in t, "anchor for the id-leak mutant moved"
open(sys.argv[2], "w").write(t.replace(old, new, 1))
PY
  # A6 needs no script mutant: GATE_OVERRIDE points the gate at a path that
  # does not exist, which is what an unavailable gate looks like in production.
}

run_controls() {
  local src="${1:-$SCRIPT}"
  PASS=0; FAIL=0; DIED=()
  build_mutants "$src"
  expect_finding "empty-population    (all held-out rows reassigned)" \
    "$src" "$SCRATCH/a1" "blind population is exhausted"
  expect_finding "population-mismatch (one row hidden from the price)" \
    "$src" "$SCRATCH/a2" "population disagreement"
  expect_finding "recycled-family     (a spent family put back)" \
    "$src" "$SCRATCH/a3" "cannot re-enter the blind population"
  expect_finding "id-leak             (row ids printed, not counted)" \
    "$SCRATCH/a5.py" "$AUTOGEN" "reached this script's own output"
  GATE_OVERRIDE="$ROOT/scripts/no-such-isolation-gate.py" \
    expect_finding "gate-unavailable    (isolation gate missing)" \
      "$src" "$AUTOGEN" "no gate was shown to share"
}

guard_deletion() {
  local ids rc_all=0
  # `empty-family` has no control: a zero-row family cannot be constructed from
  # the manifests, because a family EXISTS in this derivation only by having a
  # held-out row. It is reported here as untested rather than left implied.
  ids="$(grep -o '# GUARD:[a-z-]*' "$SCRIPT" | sed 's/# GUARD://' | sort -u \
         | grep -v '^empty-family$')"
  echo "Guard-deletion table (delete one guard, expect EXACTLY ONE control to die)"
  echo
  printf '  %-20s %-10s %-10s %s\n' guard predicted ran verdict
  printf '  %-20s %-10s %-10s %s\n' -------------------- ---------- ---------- -------
  for id in $ids; do
    grep -v "# GUARD:$id\$" "$SCRIPT" >"$SCRATCH/nog.py"
    if ! python3 -c "import ast,sys; ast.parse(open(sys.argv[1]).read())" "$SCRATCH/nog.py" 2>/dev/null; then
      printf '  %-20s %-10s %-10s %s\n' "$id" 1 "n/a" "SKIPPED (deletion does not parse)"
      rc_all=1
      continue
    fi
    QUIET=1 run_controls "$SCRATCH/nog.py"
    local verdict="ok"
    if [ "$FAIL" -ne 1 ]; then verdict="WRONG"; rc_all=1; fi
    printf '  %-20s %-10s %-10s %s' "$id" 1 "$FAIL" "$verdict"
    if [ "${#DIED[@]}" -gt 0 ]; then printf '  died: %s' "${DIED[*]}"; fi
    printf '\n'
  done
  echo
  echo "  empty-family         1          n/a        UNTESTED (see comment: not constructible)"
  echo
  return $rc_all
}

build_inputs

echo "Unmutated script, no environment override:"
env -u AXEYUM_HOLDOUT_PRICE_AUTOGEN -u AXEYUM_HOLDOUT_PRICE_GATE python3 "$SCRIPT" --check >"$SCRATCH/clean" 2>&1
CLEAN=$?
if [ "$CLEAN" -eq 0 ] && grep -F "No findings." "$SCRATCH/clean" >/dev/null; then
  echo "  PASS  clean run is green"
else
  echo "  FAIL  clean run: exit=$CLEAN"
  tail -20 "$SCRATCH/clean"
  exit 1
fi
echo

if [ "${1:-}" = "--guard-deletion" ]; then
  guard_deletion
  exit $?
fi

echo "Controls (each mutant must produce its OWN guard's finding):"
run_controls
echo
echo "controls: $PASS passed, $FAIL failed"
[ "$FAIL" -eq 0 ] || exit 1
