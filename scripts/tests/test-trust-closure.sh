#!/usr/bin/env bash
# Controls for `scripts/check-trust-closure.py` (roadmap phase S2).
#
# The phase exit is that target injection, indirect target injection, axiom
# insertion, and checker-population deletion each fail through a DIFFERENT
# guard. "Different" is the operative word and a naive reading would pass with
# four mutations dying to one shared check -- six of seven guards in one suite
# in this repository were once removable with everything still green, because
# they all rejected through one path.
#
# So this does two things prose cannot:
#
#   1. Every case asserts an EXACT failure tag, not merely a nonzero exit. Two
#      guards that both reject are not the same guard, and only the tag can
#      tell them apart.
#   2. It then DELETES each guard's rejection, one at a time, in a scratch copy
#      of the script, and requires that exactly one case dies. A mutation that
#      kills two means the cases are not separating what they claim to; a
#      mutation that kills none means the guard is unreachable and should be
#      deleted rather than kept as decoration.
#
# The mutation is applied in a COPY under a scratch root, never in the shared
# checkout: editing a tracked source file in place breaks every other lane's
# build for as long as the mutant is on disk, and the failures it causes look
# like their bug.
#
# `__pycache__` is cleared between iterations. Python caches bytecode on
# (mtime in whole SECONDS, size), and mutation produces equal-size mutants by
# construction, written back to back -- so a hand loop reliably reports the
# PREVIOUS mutant's result unless the cache is cleared.
#
#   bash scripts/tests/test-trust-closure.sh
#
# Exit 0 when every case behaves and every mutation kills exactly one.

set -u -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SUBJECT="$ROOT/scripts/check-trust-closure.py"
LANE="${AXEYUM_AGENT:-unowned}"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/trust-closure-controls-$LANE-XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

PASS=0
FAIL=0
FAILED_NAMES=()

note() { printf '%s\n' "$*"; }

# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------
#
# A five-declaration environment, deliberately tiny so that every guard's
# population is visible by eye:
#
#   T.target -> T.helper -> T.base      (the subject and its honest closure)
#   T.twin                              (SAME canonical type as T.target, so an
#                                        identity class of size 2 exists and the
#                                        alias guard has something to scan --
#                                        but T.twin is NOT in T.target's closure,
#                                        so the baseline is green)
#   T.assumed                           (an Axiom, reachable from nothing)
#
# The projection's columns are `kernel_declaration_projection`'s own:
# label, kind, name, footprint-size, type-deps, direct-deps, theorem-deps,
# canonical type.

write_baseline_projection() {
  printf '%s\n' \
    "fx	theorem	T.target	0		T.helper	T.helper	TYPE-A" \
    "fx	theorem	T.helper	0		T.base	T.base	TYPE-B" \
    "fx	theorem	T.base	0				TYPE-C" \
    "fx	theorem	T.twin	0				TYPE-A" \
    "fx	axiom	T.assumed	1				TYPE-D" \
    > "$1"
}

write_baseline_facts() {
  mkdir -p "$1"
  cat > "$1/F-target.json" <<'JSON'
{
  "id": "F:target",
  "proof_route": "kernel-lean",
  "epistemic_status": "proved",
  "formal": { "kernel_theorem": "T.target" },
  "depends_on": [],
  "evidence": [{ "id": "e", "check_status": "checked", "checker_command": "true" }]
}
JSON
  cat > "$1/F-twin.json" <<'JSON'
{
  "id": "F:twin",
  "proof_route": "kernel-lean",
  "epistemic_status": "proved",
  "formal": { "kernel_theorem": "T.twin" },
  "depends_on": [],
  "evidence": [{ "id": "e", "check_status": "checked", "checker_command": "true" }]
}
JSON
}

# `new_case <dir>` lays down the clean fixture and generates the pinned
# artifacts FROM IT, so every case starts from a state the subject calls green.
new_case() {
  local dir="$1"
  mkdir -p "$dir/artifacts"
  write_baseline_projection "$dir/projection.tsv"
  write_baseline_facts "$dir/facts"
  python3 "$SCRIPT" \
    --projection "$dir/projection.tsv" \
    --facts "$dir/facts" \
    --population "$dir/artifacts/population.json" \
    --identity-map "$dir/artifacts/identity-map.tsv" \
    --equivalent-pairs "$dir/artifacts/equivalent-pairs.tsv" \
    --update > /dev/null
  local status=$?
  if [ "$status" -ne 0 ]; then
    note "  fixture --update failed with status $status"
    return 1
  fi
  return 0
}

run_case() {
  local dir="$1"
  python3 "$SCRIPT" \
    --projection "$dir/projection.tsv" \
    --facts "$dir/facts" \
    --population "$dir/artifacts/population.json" \
    --identity-map "$dir/artifacts/identity-map.tsv" \
    --equivalent-pairs "$dir/artifacts/equivalent-pairs.tsv" \
    > "$dir/out.txt" 2> "$dir/err.txt"
  echo $? > "$dir/status"
}

# ---------------------------------------------------------------------------
# The cases. Each prints PASS/FAIL and records its name.
#
# `expect_tag` asserts BOTH a nonzero exit and the exact tag, because a nonzero
# exit alone cannot distinguish which guard rejected -- which is the entire
# question this phase exists to answer.
# ---------------------------------------------------------------------------

fixture_failed() {
  FAIL=$((FAIL + 1))
  FAILED_NAMES+=("$1")
  note "  FAIL $1: the clean fixture would not even generate its pins"
}

expect_clean() {
  local name="$1" dir="$2"
  local status
  status="$(cat "$dir/status")"
  if [ "$status" = "0" ]; then
    PASS=$((PASS + 1))
    return 0
  fi
  FAIL=$((FAIL + 1))
  FAILED_NAMES+=("$name")
  note "  FAIL $name: expected exit 0, got $status"
  sed 's/^/    /' "$dir/err.txt"
  return 1
}

expect_tag() {
  local name="$1" dir="$2" tag="$3"
  local status hits
  status="$(cat "$dir/status")"
  hits="$(/usr/bin/grep -cF "$tag" "$dir/err.txt")"
  if [ "$status" != "0" ] && [ "$hits" -ge 1 ]; then
    PASS=$((PASS + 1))
    return 0
  fi
  FAIL=$((FAIL + 1))
  FAILED_NAMES+=("$name")
  note "  FAIL $name: expected nonzero exit and tag $tag; got status=$status hits=$hits"
  sed 's/^/    /' "$dir/err.txt"
  return 1
}

# ---------- case bodies, each self-contained ----------

case_baseline() {  # the honest environment must be accepted
  local dir="$WORK/$1/baseline"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  run_case "$dir"; expect_clean baseline "$dir"
}

case_target_injection() {  # M1 -- guard_self_occurrence
  local dir="$WORK/$1/target-injection"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  # T.target now depends on itself, directly.
  printf '%s\n' "fx	theorem	T.target	0		T.helper,T.target	T.helper	TYPE-A" \
    > "$dir/p.tmp"
  awk -F'\t' '$3 != "T.target"' "$dir/projection.tsv" >> "$dir/p.tmp"
  mv "$dir/p.tmp" "$dir/projection.tsv"
  run_case "$dir"; expect_tag target-injection "$dir" "TARGET-IN-ITS-OWN-CLOSURE"
}

case_indirect_target_injection() {  # M2 -- guard_alias_occurrence, unlisted pair
  local dir="$WORK/$1/indirect-target-injection"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  # T.helper now pulls in T.twin, which states T.target's own proposition.
  printf '%s\n' "fx	theorem	T.helper	0		T.base,T.twin	T.base	TYPE-B" \
    > "$dir/p.tmp"
  awk -F'\t' '$3 != "T.helper"' "$dir/projection.tsv" >> "$dir/p.tmp"
  mv "$dir/p.tmp" "$dir/projection.tsv"
  run_case "$dir"; expect_tag indirect-target-injection "$dir" "EQUIVALENT-IN-CLOSURE"
}

case_stale_disclosure() {  # M2b -- guard_alias_occurrence, stale entry
  local dir="$WORK/$1/stale-disclosure"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  # A disclosure for a pair the environment does not exhibit. Progress that is
  # not recorded is drift waiting to happen, so it must reject too.
  printf '%s\n' "F:target	T.target	T.twin" >> "$dir/artifacts/equivalent-pairs.tsv"
  run_case "$dir"; expect_tag stale-disclosure "$dir" "STALE-DISCLOSURE"
}

case_axiom_insertion() {  # M3 -- guard_forbidden_trust, axiom branch
  local dir="$WORK/$1/axiom-insertion"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  printf '%s\n' "fx	theorem	T.base	0		T.assumed		TYPE-C" > "$dir/p.tmp"
  awk -F'\t' '$3 != "T.base"' "$dir/projection.tsv" >> "$dir/p.tmp"
  mv "$dir/p.tmp" "$dir/projection.tsv"
  run_case "$dir"; expect_tag axiom-insertion "$dir" "AXIOM-IN-CLOSURE"
}

case_unowned_opaque() {  # M3b -- guard_forbidden_trust, opaque/quotient branch
  local dir="$WORK/$1/unowned-opaque"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  # `Opaque` has no proof body and `Quotient` admits `Quot.sound`, so both are
  # trusted surface even though the environment today contains zero of each.
  # Without this case that half of the guard is never executed by anything.
  printf '%s\n' \
    "fx	theorem	T.base	0		T.sealed		TYPE-C" \
    "fx	opaque	T.sealed	0				TYPE-E" > "$dir/p.tmp"
  awk -F'\t' '$3 != "T.base"' "$dir/projection.tsv" >> "$dir/p.tmp"
  mv "$dir/p.tmp" "$dir/projection.tsv"
  run_case "$dir"; expect_tag unowned-opaque "$dir" "UNOWNED-TRUSTED-SURFACE"
}

case_population_deletion_empty() {  # M4 -- guard_population, empty branch
  local dir="$WORK/$1/population-empty"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  rm -f "$dir"/facts/*.json
  run_case "$dir"; expect_tag population-empty "$dir" "EMPTY-POPULATION"
}

case_population_deletion_floor() {  # M4b -- guard_population, floor branch
  local dir="$WORK/$1/population-floor"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  # One subject removed, not all: the count drops without reaching zero, which
  # is the realistic shape of a checker population quietly shrinking.
  rm -f "$dir/facts/F-twin.json"
  run_case "$dir"; expect_tag population-floor "$dir" "POPULATION-BELOW-FLOOR"
}

case_subject_absent() {  # M4c -- guard_population, absent-subject branch
  local dir="$WORK/$1/subject-absent"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  # The declaration is renamed out from under the fact. The COUNT of facts is
  # unchanged, so no floor can see this; only naming the environment can.
  awk -F'\t' '$3 != "T.twin"' "$dir/projection.tsv" > "$dir/p.tmp"
  printf '%s\n' "fx	theorem	T.twin_renamed	0				TYPE-A" >> "$dir/p.tmp"
  mv "$dir/p.tmp" "$dir/projection.tsv"
  run_case "$dir"; expect_tag subject-absent "$dir" "SUBJECT-ABSENT"
}

case_identity_map_drift() {  # M5 -- the derived map is pinned for review
  local dir="$WORK/$1/identity-drift"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  # T.twin stops stating T.target's proposition: the class vanishes. A class
  # appearing or vanishing is a review event either way.
  awk -F'\t' '$3 != "T.twin"' "$dir/projection.tsv" > "$dir/p.tmp"
  printf '%s\n' "fx	theorem	T.twin	0				TYPE-Z" >> "$dir/p.tmp"
  mv "$dir/p.tmp" "$dir/projection.tsv"
  run_case "$dir"; expect_tag identity-map-drift "$dir" "IDENTITY-MAP-DRIFT"
}

case_scanned_nothing() {  # M6 -- zero executed cases is failure
  local dir="$WORK/$1/scanned-nothing"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  rm -f "$dir"/facts/*.json
  run_case "$dir"; expect_tag scanned-nothing "$dir" "GUARD-SCANNED-NOTHING"
}

case_pin_missing() {  # M7 -- an absent pin is unenforced, not satisfied
  local dir="$WORK/$1/pin-missing"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  rm -f "$dir/artifacts/population.json"
  run_case "$dir"; expect_tag pin-missing "$dir" "POPULATION-PIN-MISSING"
}

case_disclosure_missing() {  # M8 -- ditto for the equivalence backlog
  local dir="$WORK/$1/disclosure-missing"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  rm -f "$dir/artifacts/equivalent-pairs.tsv"
  run_case "$dir"; expect_tag disclosure-missing "$dir" "EQUIVALENT-PAIRS-MISSING"
}

# A POSITIVE CONTROL AGAINST THE REAL ENVIRONMENT, not a fixture.
#
# ADR-0716 rests on `Nat.le_total`, `Int.le_total` and `Rat.le_total` being
# three proved theorems while `CReal.le_total` is absent. An identity map that
# normalized carriers would collapse the first three into one class and this
# guard would start rejecting correct facts. Nothing in the fixture suite can
# see that, because a fixture's types are whatever this file writes.
#
# Skipped, loudly, when no captured projection is available -- and a skip is
# reported as a skip, never counted as a pass.
case_carrier_asymmetry() {
  local projection="${AXEYUM_TRUST_CLOSURE_PROJECTION:-}"
  if [ -z "$projection" ] || [ ! -f "$projection" ]; then
    if [ "$1" = "base" ]; then
      note "  SKIP carrier-asymmetry (set AXEYUM_TRUST_CLOSURE_PROJECTION to a"
      note "       kernel_declaration_projection capture to run it)"
    fi
    return 0
  fi
  local dir="$WORK/$1/carrier-asymmetry"
  mkdir -p "$dir"
  if python3 "$WORK/carrier_asymmetry.py" "$SCRIPT" "$projection" \
      > "$dir/out.txt" 2>&1; then
    PASS=$((PASS + 1))
  else
    FAIL=$((FAIL + 1))
    FAILED_NAMES+=("carrier-asymmetry")
    note "  FAIL carrier-asymmetry"
    sed 's/^/    /' "$dir/out.txt"
  fi
}

case_empty_projection() {  # an empty environment must not pass vacuously
  local dir="$WORK/$1/empty-projection"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  : > "$dir/projection.tsv"
  run_case "$dir"; expect_tag empty-projection "$dir" "the projection is empty"
}

case_coverage_floor() {  # M4d -- guard_population, ratio branch
  local dir="$WORK/$1/coverage-floor"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  # A kernel-route fact that resolves to no declaration at all. The subject
  # COUNT does not fall, so no count floor can see it; only the ratio can. This
  # is the shape of a checker population being diluted rather than deleted.
  cat > "$dir/facts/F-unbound.json" <<'JSON'
{
  "id": "F:unbound",
  "proof_route": "kernel-lean",
  "epistemic_status": "proved",
  "formal": { "kernel_theorem": null },
  "depends_on": [],
  "evidence": [{ "id": "e", "check_status": "checked", "checker_command": "true" }]
}
JSON
  run_case "$dir"; expect_tag coverage-floor "$dir" "COVERAGE-BELOW-FLOOR"
}

case_identity_map_missing() {  # M5b -- an absent map is unenforced, not satisfied
  local dir="$WORK/$1/identity-map-missing"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  rm -f "$dir/artifacts/identity-map.tsv"
  run_case "$dir"; expect_tag identity-map-missing "$dir" "IDENTITY-MAP-MISSING"
}

CASES=(
  case_baseline
  case_target_injection
  case_indirect_target_injection
  case_stale_disclosure
  case_axiom_insertion
  case_unowned_opaque
  case_population_deletion_empty
  case_population_deletion_floor
  case_subject_absent
  case_identity_map_drift
  case_scanned_nothing
  case_pin_missing
  case_disclosure_missing
  case_empty_projection
  case_coverage_floor
  case_identity_map_missing
  case_carrier_asymmetry
)

# Case name -> the mutation expected to kill it, and the anchor that mutation
# rewrites. Anchors are the guard's own rejection CONDITION; replacing it with
# `if False:` removes the rejection while leaving the scan (and therefore the
# scanned counts) intact, so a mutation cannot be killed by the
# zero-executed-cases meta-guard instead of by the case that names it.
MUTATION_NAMES=(
  self_occurrence
  alias_unlisted
  alias_stale
  trust_unowned
  trust_axiom
  population_empty
  population_floor
  population_absent
  identity_drift
  scanned_nothing
  population_pin_missing
  disclosure_missing
  empty_projection
  coverage_floor
  identity_map_missing
)
MUTATION_ANCHORS=(
  "        if name in reach.get(name, frozenset()):"
  "        if (ident, name, found) in disclosed:"
  "    stale = sorted(disclosed - set(observed))"
  "        if unowned:"
  "        if reached:"
  "    if count == 0:"
  "    if count < floor:"
  "    for ident, name in subjects.absent:"
  "        if want != have:"
  "        if result.scanned == 0:"
  "    if not pinned:"
  "    if disclosure_failure is not None:"
  "    if not decls:"
  "    if ratio < ratio_floor - 1e-9:"
  "    if not identity_map_present:"
)
MUTATION_REPLACEMENTS=(
  "        if False:"
  "        if True:"
  "    stale = []"
  "        if False:"
  "        if False:"
  "    if False:"
  "    if False:"
  "    for ident, name in []:"
  "        if False:"
  "        if False:"
  "    if False:"
  "    if False:"
  "    if False:"
  "    if False:"
  "    if False:"
)

run_all_cases() {
  local tag="$1"
  PASS=0; FAIL=0; FAILED_NAMES=()
  local c
  for c in "${CASES[@]}"; do
    "$c" "$tag"
  done
}

# ---------------------------------------------------------------------------
# 1. Baseline: every case behaves against the unmutated subject.
# ---------------------------------------------------------------------------
mkdir -p "$WORK/scripts"
cp "$ROOT/scripts/check-fact-depends-derived.py" "$WORK/scripts/"
cp "$SUBJECT" "$WORK/scripts/check-trust-closure.py"
SCRIPT="$WORK/scripts/check-trust-closure.py"

cat > "$WORK/carrier_asymmetry.py" <<'PY'
"""ADR-0716's carrier asymmetry, checked against the REAL environment.

`Nat.le_total`, `Int.le_total` and `Rat.le_total` are three proved theorems
here while `CReal.le_total` is absent, and that asymmetry is load-bearing. An
identity map that normalized carriers would collapse the first three into one
class and this guard would start rejecting correct facts. No fixture can see
that, because a fixture's types are whatever the suite writes.
"""
import importlib.util
import pathlib
import sys

spec = importlib.util.spec_from_file_location("tc", sys.argv[1])
tc = importlib.util.module_from_spec(spec)
sys.modules["tc"] = tc
spec.loader.exec_module(tc)

decls = tc.parse_projection(pathlib.Path(sys.argv[2]).read_text(encoding="utf-8"))
classes = tc.identity_classes(decls)
member_of = {n: c for c in classes.values() for n in c}
problems = []
# The claim is about CARRIERS, and the first draft of this control overreached
# by requiring `Int.le_total` to be in no class at all. It is in one: with
# `Int.Characterization.le_total`, the same proposition over the same carrier
# under two names -- which the map is RIGHT to merge, and which is already on
# the disclosed backlog. So assert exactly what ADR-0716 rests on: no two of
# the three CARRIERS are merged with each other.
carriers = ["Nat", "Int", "Rat"]
names = [f"{c}.le_total" for c in carriers]
for name in names:
    if name not in decls:
        problems.append(f"{name} is not in the environment; the control is aimed wrong")
for i, left in enumerate(names):
    for right in names[i + 1:]:
        if right in member_of.get(left, []):
            problems.append(
                f"{left} and {right} share an identity class; ADR-0716's carrier "
                f"asymmetry has been collapsed"
            )
if "CReal.le_total" in decls:
    problems.append(
        "CReal.le_total now EXISTS; ADR-0716's asymmetry has changed and this "
        "control needs rewriting, not deleting"
    )
# A positive control for the control: three absences from an EMPTY map would be
# no evidence at all.
if not classes:
    problems.append(
        "the identity map is empty, so finding le_total absent from it proves nothing"
    )
for problem in problems:
    print(problem)
print(f"carrier-asymmetry: {len(classes)} identity classes scanned")
raise SystemExit(1 if problems else 0)
PY

note "== baseline =="
run_all_cases base
BASE_PASS=$PASS
BASE_FAIL=$FAIL
if [ "$BASE_FAIL" -ne 0 ]; then
  note "TRUST_CLOSURE_CONTROLS|BASELINE FAILED: ${FAILED_NAMES[*]}"
  exit 1
fi
if [ "$BASE_PASS" -eq 0 ]; then
  note "TRUST_CLOSURE_CONTROLS|BASELINE ran ZERO cases -- that is a failure, not a pass"
  exit 1
fi
note "baseline: $BASE_PASS case(s) behaved"

# ---------------------------------------------------------------------------
# 2. Mutations: delete each guard's rejection; exactly one case must die.
# ---------------------------------------------------------------------------
MUT_FAIL=0
SUMMARY=()
for i in "${!MUTATION_NAMES[@]}"; do
  name="${MUTATION_NAMES[$i]}"
  anchor="${MUTATION_ANCHORS[$i]}"
  replacement="${MUTATION_REPLACEMENTS[$i]}"

  # Python caches bytecode on (mtime seconds, size); mutants are written back
  # to back and are often equal in size, so a stale cache would report the
  # PREVIOUS mutant's result.
  find "$WORK" -name __pycache__ -type d -exec rm -rf {} + 2>/dev/null

  cp "$SUBJECT" "$SCRIPT"
  hits="$(/usr/bin/grep -cxF "$anchor" "$SCRIPT")"
  if [ "$hits" != "1" ]; then
    note "== mutation $name: ANCHOR MATCHED $hits TIMES, expected exactly 1 =="
    note "   anchor: $anchor"
    note "   a stale anchor silently measures nothing; fix it rather than widening it"
    MUT_FAIL=$((MUT_FAIL + 1))
    continue
  fi
  python3 - "$SCRIPT" "$anchor" "$replacement" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
lines = path.read_text(encoding="utf-8").splitlines(keepends=True)
anchor, replacement = sys.argv[2], sys.argv[3]
out = []
for line in lines:
    out.append(replacement + "\n" if line.rstrip("\n") == anchor else line)
path.write_text("".join(out), encoding="utf-8")
PY

  run_all_cases "mut-$name"
  killed=("${FAILED_NAMES[@]:-}")
  killed_count=$FAIL
  if [ "$killed_count" -eq 1 ]; then
    SUMMARY+=("$name KILLED ${killed[0]}")
  elif [ "$killed_count" -eq 0 ]; then
    SUMMARY+=("$name SURVIVED -- no case died; the guard is unreachable or untested")
    MUT_FAIL=$((MUT_FAIL + 1))
  else
    SUMMARY+=("$name KILLED $killed_count cases: ${killed[*]} -- not distinct")
    MUT_FAIL=$((MUT_FAIL + 1))
  fi
done

cp "$SUBJECT" "$SCRIPT"

note ""
note "== mutation kill sets =="
for line in "${SUMMARY[@]}"; do note "  $line"; done

note ""
note "TRUST_CLOSURE_CONTROLS|cases=${#CASES[@]}|mutations=${#MUTATION_NAMES[@]}|not_exactly_one=$MUT_FAIL"
if [ "$MUT_FAIL" -ne 0 ]; then
  exit 1
fi
exit 0
