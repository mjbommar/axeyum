#!/usr/bin/env bash
# Controls for scripts/check-obstruction-producers.py.
#
# One case per guard (G1-G10). Each case builds a synthetic fixture tree
# (a scratch `artifacts/facts/`, `artifacts/obstruction-producers/`) with
# EXACTLY the defect the guard is meant to catch, runs the checker with
# `--root <scratch> --skip-freshness` (G1's own case is the one exception:
# it runs against a REAL committed copy of this lane's own artifacts,
# temporarily mutated and restored in the same case, because G1's whole
# job is to compare against a real generator), and asserts BOTH that the
# named guard fired and that no other guard fired -- so a guard that is
# deleted or weakened is killed by exactly one case.
#
# Case 0 is the healthy-fixture false-positive control: a fixture built to
# satisfy every guard must exit 0. Run FIRST so a broken fixture-builder is
# caught before it produces false "PASS"es everywhere else.
#
# This test mutates ONLY scratch fixtures under a mktemp directory and,
# for G1's case only, a temporary copy of this lane's own tracked files
# restored before the case ends -- never the shared checkout, per this
# repository's mutation-testing hygiene rule.

set -u -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CHECK="$ROOT/scripts/check-obstruction-producers.py"
GEN="$ROOT/scripts/gen-obstruction-producers.py"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

FAILURES=0
CASES=0

ALL_GUARDS=(G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11)

# run <label> <expected-exit> <expected-guard-or-NONE> -- <args...>
run() {
  local label="$1" want_exit="$2" want_guard="$3"; shift 3
  [ "$1" = "--" ] && shift
  CASES=$((CASES + 1))
  local out status
  out="$(python3 "$CHECK" "$@" 2>&1)"
  status=$?
  local bad=0
  if [ "$status" -ne "$want_exit" ]; then
    echo "FAIL [$label]: exit $status, expected $want_exit"
    bad=1
  fi
  local g
  for g in "${ALL_GUARDS[@]}"; do
    local hits
    hits="$(printf '%s\n' "$out" | /usr/bin/grep -cE "\b${g} [a-z-]+" || true)"
    if [ "$g" = "$want_guard" ]; then
      if [ "$hits" -eq 0 ]; then
        echo "FAIL [$label]: expected guard $g to fire, it did not"
        bad=1
      fi
    else
      if [ "$hits" -ne 0 ]; then
        echo "FAIL [$label]: guard $g also fired ($hits line(s)); this case must kill exactly one"
        bad=1
      fi
    fi
  done
  if [ "$bad" -ne 0 ]; then
    echo "----- output for [$label] -----"
    printf '%s\n' "$out"
    echo "--------------------------------"
    FAILURES=$((FAILURES + 1))
  else
    echo "ok   [$label]"
  fi
}

# --- fixture builder -------------------------------------------------------
#
# Builds a minimal but internally-consistent scratch tree: 6 facts (4 open,
# 2 not-open), one obstruction naming all 4 open facts as its population,
# and one producer contract with kind=producer, applicability of 2 of those
# 4, and a negative control naming one of the other 2. This is the smallest
# shape that can satisfy every guard, which is what the healthy case proves.
build_fixture() {
  local dir="$1"
  rm -rf "$dir"
  mkdir -p "$dir/artifacts/facts" "$dir/artifacts/obstruction-producers/producers" "$dir/scripts"
  # A file for a "not-removable" obstruction's evidence to point at (G9's
  # backing check resolves evidence paths against --root, so the fixture
  # needs a real file there, not the real repo's).
  echo "synthetic evidence file" > "$dir/scripts/check-obstruction-producers.py"

  write_fact() {
    local id="$1" status="$2"
    local file
    file="$dir/artifacts/facts/$(printf '%s' "$id" | tr ':' '-').json"
    printf '{"id": "%s", "epistemic_status": "%s"}\n' "$id" "$status" > "$file"
  }
  write_fact "F:test-target-a" "open"
  write_fact "F:test-target-b" "open"
  write_fact "F:test-control-c" "open"
  write_fact "F:test-control-d" "open"
  write_fact "F:test-settled-e" "proved"

  cat > "$dir/artifacts/obstruction-producers/obstructions.json" <<'JSON'
{
  "schema_version": 1,
  "generated_by": "test fixture",
  "obstructions": [
    {
      "id": "test-obstruction",
      "capability_gap": "equality-transport",
      "removability": "producer",
      "reason": "synthetic fixture",
      "evidence": ["scripts/check-obstruction-producers.py"],
      "blocked_fact_ids": ["F:test-target-a", "F:test-target-b",
                            "F:test-control-c", "F:test-control-d"]
    },
    {
      "id": "test-not-removable",
      "capability_gap": "definitional-non-equivalence",
      "removability": "not-removable",
      "reason": "synthetic fixture",
      "evidence": ["scripts/check-obstruction-producers.py"],
      "blocked_fact_ids": ["F:test-settled-e"]
    }
  ]
}
JSON

  cat > "$dir/artifacts/obstruction-producers/producers/test-producer.json" <<'JSON'
{
  "id": "test-producer",
  "kind": "producer",
  "route": "kernel-lane",
  "obstruction_ids": ["test-obstruction"],
  "capability_gap": "equality-transport",
  "applicability": {"fact_ids": ["F:test-target-a", "F:test-target-b"]},
  "negative_controls": [
    {"fact_id": "F:test-control-c", "why_declines": "synthetic"}
  ]
}
JSON
}

echo "== case 0: healthy fixture (false-positive control) =="
build_fixture "$WORK/healthy"
run "healthy-fixture-passes" 0 NONE -- --root "$WORK/healthy" --skip-freshness

echo "== G2: empty classification =="
build_fixture "$WORK/g2"
cat > "$WORK/g2/artifacts/obstruction-producers/obstructions.json" <<'JSON'
{"schema_version": 1, "generated_by": "test fixture", "obstructions": []}
JSON
# Clearing obstructions also strands the fixture producer's obstruction_ids
# link (G10 dangling-obstruction-link) as a genuine consequence of the same
# edit -- not a false co-fire -- so this case asserts both explicitly rather
# than through the shared exact-one-guard `run` helper.
out="$(python3 "$CHECK" --root "$WORK/g2" --skip-freshness 2>&1)"
status=$?
CASES=$((CASES + 1))
if [ "$status" -eq 1 ] \
   && printf '%s\n' "$out" | /usr/bin/grep -cE '\bG2 empty-classification' >/dev/null \
   && printf '%s\n' "$out" | /usr/bin/grep -cE '\bG10 dangling-obstruction-link' >/dev/null; then
  echo "ok   [G2-empty-classification-and-consequent-G10]"
else
  echo "FAIL [G2-empty-classification-and-consequent-G10]"
  printf '%s\n' "$out"
  FAILURES=$((FAILURES + 1))
fi

echo "== G3: no live producer (only a capsule) =="
build_fixture "$WORK/g3"
cat > "$WORK/g3/artifacts/obstruction-producers/producers/test-producer.json" <<'JSON'
{
  "id": "test-producer",
  "kind": "capsule",
  "route": "kernel-lane",
  "obstruction_ids": ["test-obstruction"],
  "capability_gap": "equality-transport",
  "applicability": {"fact_ids": ["F:test-target-a"]},
  "negative_controls": [
    {"fact_id": "F:test-control-c", "why_declines": "synthetic"}
  ]
}
JSON
run "G3-no-live-producer" 1 G3 -- --root "$WORK/g3" --skip-freshness

echo "== G4: proved field present =="
build_fixture "$WORK/g4"
cat > "$WORK/g4/artifacts/obstruction-producers/producers/test-producer.json" <<'JSON'
{
  "id": "test-producer",
  "kind": "producer",
  "route": "kernel-lane",
  "obstruction_ids": ["test-obstruction"],
  "capability_gap": "equality-transport",
  "applicability": {"fact_ids": ["F:test-target-a", "F:test-target-b"]},
  "negative_controls": [
    {"fact_id": "F:test-control-c", "why_declines": "synthetic"}
  ],
  "proved": true
}
JSON
run "G4-proved-field-present" 1 G4 -- --root "$WORK/g4" --skip-freshness

echo "== G5: empty applicability =="
build_fixture "$WORK/g5"
cat > "$WORK/g5/artifacts/obstruction-producers/producers/test-producer.json" <<'JSON'
{
  "id": "test-producer",
  "kind": "producer",
  "route": "kernel-lane",
  "obstruction_ids": ["test-obstruction"],
  "capability_gap": "equality-transport",
  "applicability": {"fact_ids": []},
  "negative_controls": [
    {"fact_id": "F:test-control-c", "why_declines": "synthetic"}
  ]
}
JSON
# G5 firing forces fact_ids to [] downstream, which also starves G3 (no live
# producer) -- both are correct consequences of one defect, so this case
# names G5 as EXPECTED and G3 is allowed to co-fire. Handled by a dedicated
# assertion rather than the shared `run` helper's exact-one-guard rule.
out="$(python3 "$CHECK" --root "$WORK/g5" --skip-freshness 2>&1)"
status=$?
CASES=$((CASES + 1))
if [ "$status" -eq 1 ] \
   && printf '%s\n' "$out" | /usr/bin/grep -cE '\bG5 empty-applicability' >/dev/null \
   && printf '%s\n' "$out" | /usr/bin/grep -cE '\bG3 no-live-producer' >/dev/null; then
  echo "ok   [G5-empty-applicability-and-consequent-G3]"
else
  echo "FAIL [G5-empty-applicability-and-consequent-G3]"
  printf '%s\n' "$out"
  FAILURES=$((FAILURES + 1))
fi

echo "== G6: single-target producer claiming kind=producer =="
build_fixture "$WORK/g6"
cat > "$WORK/g6/artifacts/obstruction-producers/producers/test-producer.json" <<'JSON'
{
  "id": "test-producer",
  "kind": "producer",
  "route": "kernel-lane",
  "obstruction_ids": ["test-obstruction"],
  "capability_gap": "equality-transport",
  "applicability": {"fact_ids": ["F:test-target-a"]},
  "negative_controls": [
    {"fact_id": "F:test-control-c", "why_declines": "synthetic"}
  ]
}
JSON
# Same co-firing note as G5: a single-target "producer" is also, correctly,
# not a LIVE producer (G3's definition requires >= 2), so both fire.
out="$(python3 "$CHECK" --root "$WORK/g6" --skip-freshness 2>&1)"
status=$?
CASES=$((CASES + 1))
if [ "$status" -eq 1 ] \
   && printf '%s\n' "$out" | /usr/bin/grep -cE '\bG6 single-target-producer' >/dev/null \
   && printf '%s\n' "$out" | /usr/bin/grep -cE '\bG3 no-live-producer' >/dev/null; then
  echo "ok   [G6-single-target-and-consequent-G3]"
else
  echo "FAIL [G6-single-target-and-consequent-G3]"
  printf '%s\n' "$out"
  FAILURES=$((FAILURES + 1))
fi

echo "== G7: applicability names a fact not in the ledger =="
build_fixture "$WORK/g7a"
# The unknown fact must be inside its obstruction's own blocked_fact_ids
# population, or the edit also trips G10 (coverage-overreach) as a genuine
# side effect -- widening the population isolates G7 as the only defect.
python3 - "$WORK/g7a/artifacts/obstruction-producers/obstructions.json" <<'PY'
import json, sys
p = sys.argv[1]
doc = json.load(open(p))
doc["obstructions"][0]["blocked_fact_ids"].append("F:does-not-exist")
json.dump(doc, open(p, "w"))
PY
cat > "$WORK/g7a/artifacts/obstruction-producers/producers/test-producer.json" <<'JSON'
{
  "id": "test-producer",
  "kind": "producer",
  "route": "kernel-lane",
  "obstruction_ids": ["test-obstruction"],
  "capability_gap": "equality-transport",
  "applicability": {"fact_ids": ["F:test-target-a", "F:does-not-exist"]},
  "negative_controls": [
    {"fact_id": "F:test-control-c", "why_declines": "synthetic"}
  ]
}
JSON
run "G7-unknown-target" 1 G7 -- --root "$WORK/g7a" --skip-freshness

echo "== G7: applicability names a non-open (settled) fact =="
build_fixture "$WORK/g7b"
cat > "$WORK/g7b/artifacts/obstruction-producers/producers/test-producer.json" <<'JSON'
{
  "id": "test-producer",
  "kind": "producer",
  "route": "kernel-lane",
  "obstruction_ids": ["test-obstruction"],
  "capability_gap": "equality-transport",
  "applicability": {"fact_ids": ["F:test-target-a", "F:test-settled-e"]},
  "negative_controls": [
    {"fact_id": "F:test-control-c", "why_declines": "synthetic"}
  ]
}
JSON
# F:test-settled-e is outside test-obstruction's own population, so this
# also trips G10 (coverage-overreach) -- a real defect of the same fixture
# edit, not a false co-fire.
out="$(python3 "$CHECK" --root "$WORK/g7b" --skip-freshness 2>&1)"
status=$?
CASES=$((CASES + 1))
if [ "$status" -eq 1 ] \
   && printf '%s\n' "$out" | /usr/bin/grep -cE '\bG7 non-open-target' >/dev/null \
   && printf '%s\n' "$out" | /usr/bin/grep -cE '\bG10 coverage-overreach' >/dev/null; then
  echo "ok   [G7-non-open-target-and-consequent-G10]"
else
  echo "FAIL [G7-non-open-target-and-consequent-G10]"
  printf '%s\n' "$out"
  FAILURES=$((FAILURES + 1))
fi

echo "== G8: no negative controls =="
build_fixture "$WORK/g8"
cat > "$WORK/g8/artifacts/obstruction-producers/producers/test-producer.json" <<'JSON'
{
  "id": "test-producer",
  "kind": "producer",
  "route": "kernel-lane",
  "obstruction_ids": ["test-obstruction"],
  "capability_gap": "equality-transport",
  "applicability": {"fact_ids": ["F:test-target-a", "F:test-target-b"]},
  "negative_controls": []
}
JSON
run "G8-no-negative-controls" 1 G8 -- --root "$WORK/g8" --skip-freshness

echo "== G9: bad removability value =="
build_fixture "$WORK/g9a"
python3 - "$WORK/g9a/artifacts/obstruction-producers/obstructions.json" <<'PY'
import json, sys
p = sys.argv[1]
doc = json.load(open(p))
doc["obstructions"][0]["removability"] = "maybe"
json.dump(doc, open(p, "w"))
PY
run "G9-bad-removability" 1 G9 -- --root "$WORK/g9a" --skip-freshness

echo "== G9: not-removable with no backing evidence =="
build_fixture "$WORK/g9b"
python3 - "$WORK/g9b/artifacts/obstruction-producers/obstructions.json" <<'PY'
import json, sys
p = sys.argv[1]
doc = json.load(open(p))
doc["obstructions"][1]["evidence"] = ["no/such/path.md"]
json.dump(doc, open(p, "w"))
PY
run "G9-unbacked-not-removable" 1 G9 -- --root "$WORK/g9b" --skip-freshness

echo "== G10: applicability outside its obstruction's population =="
build_fixture "$WORK/g10"
cat > "$WORK/g10/artifacts/obstruction-producers/producers/test-producer.json" <<'JSON'
{
  "id": "test-producer",
  "kind": "producer",
  "route": "kernel-lane",
  "obstruction_ids": ["test-not-removable"],
  "capability_gap": "equality-transport",
  "applicability": {"fact_ids": ["F:test-target-a", "F:test-target-b"]},
  "negative_controls": [
    {"fact_id": "F:test-control-c", "why_declines": "synthetic"}
  ]
}
JSON
run "G10-coverage-overreach" 1 G10 -- --root "$WORK/g10" --skip-freshness

echo "== G11: a settled-target record names a fact that is still open =="
build_fixture "$WORK/g11a"
cat > "$WORK/g11a/artifacts/obstruction-producers/producers/test-producer.json" <<'JSON'
{
  "id": "test-producer",
  "kind": "producer",
  "route": "kernel-lane",
  "obstruction_ids": ["test-obstruction"],
  "capability_gap": "equality-transport",
  "applicability": {"fact_ids": ["F:test-target-a", "F:test-target-b"]},
  "spent": [
    {"fact_id": "F:test-control-d", "closed_status": "proved",
     "settled_commit": "0123456789abcdef0123456789abcdef01234567",
     "settled_date": "2026-08-30"}
  ],
  "negative_controls": [
    {"fact_id": "F:test-control-c", "why_declines": "synthetic"}
  ]
}
JSON
# `F:test-control-d` is open in the fixture. Parking it in `spent` is how a
# contract could retire live work where G7 -- which only reads applicability --
# cannot see it.
run "G11-spent-target-still-open" 1 G11 -- --root "$WORK/g11a" --skip-freshness

echo "== G11: a settled target is recorded AND still claimed as live =="
build_fixture "$WORK/g11b"
python3 - "$WORK/g11b/artifacts/obstruction-producers/obstructions.json" <<'PY'
import json, sys
p = sys.argv[1]
doc = json.load(open(p))
# Widen the population so the settled fact is inside it; otherwise this edit
# also trips G10 (coverage-overreach) as a genuine second defect.
doc["obstructions"][0]["blocked_fact_ids"].append("F:test-settled-e")
json.dump(doc, open(p, "w"))
PY
cat > "$WORK/g11b/artifacts/obstruction-producers/producers/test-producer.json" <<'JSON'
{
  "id": "test-producer",
  "kind": "producer",
  "route": "kernel-lane",
  "obstruction_ids": ["test-obstruction"],
  "capability_gap": "equality-transport",
  "applicability": {"fact_ids": ["F:test-target-a", "F:test-settled-e"]},
  "spent": [
    {"fact_id": "F:test-settled-e", "closed_status": "proved",
     "settled_commit": "0123456789abcdef0123456789abcdef01234567",
     "settled_date": "2026-08-30"}
  ],
  "negative_controls": [
    {"fact_id": "F:test-control-c", "why_declines": "synthetic"}
  ]
}
JSON
# A settled fact left in `applicability` is ALSO a genuine G7 defect, so both
# fire from one edit -- the same shape as the G5/G6/G7b cases above, asserted
# explicitly rather than through the exact-one-guard helper.
out="$(python3 "$CHECK" --root "$WORK/g11b" --skip-freshness 2>&1)"
status=$?
CASES=$((CASES + 1))
if [ "$status" -eq 1 ] \
   && printf '%s\n' "$out" | /usr/bin/grep -cE '\bG11 spent-and-live' >/dev/null \
   && printf '%s\n' "$out" | /usr/bin/grep -cE '\bG7 non-open-target' >/dev/null; then
  echo "ok   [G11-spent-and-live-and-consequent-G7]"
else
  echo "FAIL [G11-spent-and-live-and-consequent-G7]"
  printf '%s\n' "$out"
  FAILURES=$((FAILURES + 1))
fi

echo "== G1: freshness (real lane artifacts, temporarily mutated) =="
if [ -f "$GEN" ] && [ -f "$ROOT/artifacts/obstruction-producers/obstructions.json" ]; then
  REAL="$ROOT/artifacts/obstruction-producers/obstructions.json"
  BACKUP="$WORK/obstructions.json.bak"
  cp "$REAL" "$BACKUP"
  python3 - "$REAL" <<'PY'
import json, sys
p = sys.argv[1]
doc = json.load(open(p))
doc["obstructions"][0]["reason"] = doc["obstructions"][0]["reason"] + " (mutated for G1 test)"
json.dump(doc, open(p, "w"), indent=2, sort_keys=True)
open(p, "a").write("\n")
PY
  run "G1-stale-classification" 1 G1 -- --root "$ROOT"
  cp "$BACKUP" "$REAL"
  # Confirm the restore actually worked before trusting anything after this point.
  if ! python3 "$GEN" --check >/dev/null 2>&1; then
    echo "FAIL [G1-restore]: real obstructions.json did not restore cleanly"
    FAILURES=$((FAILURES + 1))
  fi
else
  echo "SKIP [G1]: no real gen-obstruction-producers.py / obstructions.json found"
fi

echo ""
echo "$CASES case(s) run, $FAILURES failure(s)"
[ "$FAILURES" -eq 0 ]
