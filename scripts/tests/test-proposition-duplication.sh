#!/usr/bin/env bash
# Controls for `scripts/check-proposition-duplication.py` (ADR-0790).
#
# Same discipline as `scripts/tests/test-trust-closure.sh`: every case asserts
# an EXACT failure tag, not merely a nonzero exit, and then the suite DELETES
# each guard's rejection condition, one at a time, in a scratch copy of the
# script, and requires that exactly one case dies. The mutation is applied in
# a COPY under a scratch root, never in the shared checkout.
#
#   bash scripts/tests/test-proposition-duplication.sh
#
# Exit 0 when every case behaves and every mutation kills exactly one.

set -u -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SUBJECT="$ROOT/scripts/check-proposition-duplication.py"
LANE="${AXEYUM_AGENT:-unowned}"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/prop-dup-controls-$LANE-XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

PASS=0
FAIL=0
FAILED_NAMES=()

note() { printf '%s\n' "$*"; }

# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------
#
#   TYPE-A (size 2): T.a1 (canonical) <- T.a2 (equivalent_to a1)          -- clean
#   TYPE-C (size 3): T.c1 (canonical) <- T.c2, T.c3 (both equivalent_to c1) -- clean
#   TYPE-D (size 2): T.d1 (canonical) <- T.d2 (equivalent_to d1)          -- clean
#   TYPE-E (size 1): T.ext (canonical, no class -- an external target)
#   TYPE-B (size 1): T.b1 (canonical, no class -- background noise)
#
# 3 identity classes in the clean baseline (A, C, D); the floor is pinned to 3.

write_baseline_projection() {
  printf '%s\n' \
    "fx	theorem	T.a1	0				TYPE-A" \
    "fx	theorem	T.a2	0				TYPE-A" \
    "fx	theorem	T.c1	0				TYPE-C" \
    "fx	theorem	T.c2	0				TYPE-C" \
    "fx	theorem	T.c3	0				TYPE-C" \
    "fx	theorem	T.d1	0				TYPE-D" \
    "fx	theorem	T.d2	0				TYPE-D" \
    "fx	theorem	T.ext	0				TYPE-E" \
    "fx	theorem	T.b1	0				TYPE-B" \
    > "$1"
}

fact_json() {
  # fact_json <id> <kernel_theorem> <status> [equivalent_to_id]
  local id="$1" kt="$2" status="$3" eq="${4:-}"
  if [ -n "$eq" ]; then
    printf '{\n  "id": "%s",\n  "proof_route": "kernel-lean",\n  "epistemic_status": "%s",\n  "formal": { "kernel_theorem": "%s" },\n  "depends_on": [],\n  "evidence": [{ "id": "e", "check_status": "checked", "checker_command": "true" }],\n  "equivalent_to": ["%s"]\n}\n' \
      "$id" "$status" "$kt" "$eq"
  else
    printf '{\n  "id": "%s",\n  "proof_route": "kernel-lean",\n  "epistemic_status": "%s",\n  "formal": { "kernel_theorem": "%s" },\n  "depends_on": [],\n  "evidence": [{ "id": "e", "check_status": "checked", "checker_command": "true" }]\n}\n' \
      "$id" "$status" "$kt"
  fi
}

write_baseline_facts() {
  local dir="$1"
  mkdir -p "$dir"
  fact_json "F:a1" "T.a1" "proved" > "$dir/F-a1.json"
  fact_json "F:a2" "T.a2" "proved" "F:a1" > "$dir/F-a2.json"
  fact_json "F:c1" "T.c1" "proved" > "$dir/F-c1.json"
  fact_json "F:c2" "T.c2" "proved" "F:c1" > "$dir/F-c2.json"
  fact_json "F:c3" "T.c3" "proved" "F:c1" > "$dir/F-c3.json"
  fact_json "F:d1" "T.d1" "proved" > "$dir/F-d1.json"
  fact_json "F:d2" "T.d2" "proved" "F:d1" > "$dir/F-d2.json"
  fact_json "F:ext" "T.ext" "proved" > "$dir/F-ext.json"
  fact_json "F:b1" "T.b1" "proved" > "$dir/F-b1.json"
  # An unsettled fact, used only by case_target_unsettled.
  printf '{\n  "id": "F:open",\n  "proof_route": "kernel-lean",\n  "epistemic_status": "open",\n  "formal": { "kernel_theorem": null },\n  "depends_on": [],\n  "evidence": []\n}\n' > "$dir/F-open.json"
}

# `new_case <dir>` lays down the clean fixture and pins the floor FROM IT, so
# every case starts from a state the subject calls green.
new_case() {
  local dir="$1"
  mkdir -p "$dir/artifacts"
  write_baseline_projection "$dir/projection.tsv"
  write_baseline_facts "$dir/facts"
  python3 "$SCRIPT" \
    --projection "$dir/projection.tsv" \
    --facts "$dir/facts" \
    --population "$dir/artifacts/population.json" \
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
    > "$dir/out.txt" 2> "$dir/err.txt"
  echo $? > "$dir/status"
}

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

case_empty_projection() {  # guard_identity_classes_empty
  local dir="$WORK/$1/empty-projection"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  : > "$dir/projection.tsv"
  run_case "$dir"; expect_tag empty-projection "$dir" "IDENTITY-CLASSES-EMPTY"
}

case_below_floor() {  # guard_identity_classes_below_floor
  local dir="$WORK/$1/below-floor"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  # Drop TYPE-D to a singleton (remove T.d2) without touching TYPE-A/TYPE-C,
  # so classes go 3 -> 2, below the pinned floor of 3, without emptying.
  awk -F'\t' '$3 != "T.d2"' "$dir/projection.tsv" > "$dir/p.tmp"
  mv "$dir/p.tmp" "$dir/projection.tsv"
  run_case "$dir"; expect_tag below-floor "$dir" "IDENTITY-CLASSES-BELOW-FLOOR"
}

case_unlabeled_duplicate_pair() {  # guard_unlabeled_duplicate_pair
  local dir="$WORK/$1/unlabeled-pair"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  # Strip F:a2's equivalent_to -- now TYPE-A has 2 canonical (unmarked) facts.
  fact_json "F:a2" "T.a2" "proved" > "$dir/facts/F-a2.json"
  run_case "$dir"; expect_tag unlabeled-duplicate-pair "$dir" "UNLABELED-DUPLICATE-PAIR"
}

case_no_canonical_designated() {  # guard_no_canonical_designated
  local dir="$WORK/$1/no-canonical"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  # F:d1 (TYPE-D's only canonical) now ALSO points outside the class, at the
  # unrelated F:ext -- TYPE-D's class has 0 canonical members left.
  fact_json "F:d1" "T.d1" "proved" "F:ext" > "$dir/facts/F-d1.json"
  run_case "$dir"; expect_tag no-canonical-designated "$dir" "NO-CANONICAL-DESIGNATED"
}

case_target_absent() {  # guard_equivalent_to_target_absent
  local dir="$WORK/$1/target-absent"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  fact_json "F:a2" "T.a2" "proved" "F:does-not-exist" > "$dir/facts/F-a2.json"
  run_case "$dir"; expect_tag target-absent "$dir" "EQUIVALENT-TO-TARGET-ABSENT"
}

case_target_unsettled() {  # guard_equivalent_to_target_unsettled
  local dir="$WORK/$1/target-unsettled"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  fact_json "F:a2" "T.a2" "proved" "F:open" > "$dir/facts/F-a2.json"
  run_case "$dir"; expect_tag target-unsettled "$dir" "EQUIVALENT-TO-TARGET-UNSETTLED"
}

case_chain() {  # guard_equivalent_to_chain
  local dir="$WORK/$1/chain"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  # F:c3 now points at F:c2 (which itself carries equivalent_to) instead of
  # the canonical F:c1 -- a chain, A -> B -> C.
  fact_json "F:c3" "T.c3" "proved" "F:c2" > "$dir/facts/F-c3.json"
  run_case "$dir"; expect_tag chain "$dir" "EQUIVALENT-TO-CHAIN"
}

case_different_proposition() {  # guard_equivalent_to_different_proposition
  local dir="$WORK/$1/different-proposition"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  # F:d2 now claims equivalence to F:ext, a DIFFERENT canonical type
  # (TYPE-E, not TYPE-D). TYPE-D still has exactly one canonical member
  # (F:d1), so neither the unlabeled-pair nor no-canonical guard fires.
  fact_json "F:d2" "T.d2" "proved" "F:ext" > "$dir/facts/F-d2.json"
  run_case "$dir"; expect_tag different-proposition "$dir" "EQUIVALENT-TO-DIFFERENT-PROPOSITION"
}

case_shared_declaration_pair() {  # guard_shared_declaration_pair
  local dir="$WORK/$1/shared-decl"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  # Two settled facts naming ONE kernel declaration and stating the SAME
  # proposition (variable names differ, which must not matter), neither marked.
  # `guard_unlabeled_duplicate_pair` cannot see this: it groups by identity
  # CLASS -- two DIFFERENT declarations with byte-identical types -- and here
  # there is only ever one declaration to put in a class.
  printf '{\n  "id": "F:sd1",\n  "proof_route": "kernel-lean",\n  "epistemic_status": "proved",\n  "formal": { "kernel_theorem": "T.shared", "statement": "forall (n m : N), n & m = m & n" },\n  "depends_on": [],\n  "evidence": [{ "id": "e", "check_status": "checked", "checker_command": "true", "kernel_declaration": "T.shared" }]\n}\n' > "$dir/facts/F-sd1.json"
  printf '{\n  "id": "F:sd2",\n  "proof_route": "kernel-lean",\n  "epistemic_status": "proved",\n  "formal": { "kernel_theorem": "T.shared", "statement": "forall (x y : N), x & y = y & x" },\n  "depends_on": [],\n  "evidence": [{ "id": "e", "check_status": "checked", "checker_command": "true", "kernel_declaration": "T.shared" }]\n}\n' > "$dir/facts/F-sd2.json"
  run_case "$dir"; expect_tag shared-declaration-pair "$dir" "SHARED-DECLARATION-PAIR"
}

case_canonical_is_the_dependency() {  # guard_canonical_is_the_dependency
  local dir="$WORK/$1/canonical-direction"; new_case "$dir" || { fixture_failed "${FUNCNAME[0]}"; return 1; }
  # Give TYPE-D's CANONICAL member a direct dependency on its own marked
  # class-mate: `T.d1`'s closure now reaches `T.d2`, so canonicity sits on the
  # wrapper instead of on the dependency (ADR-0790, ADR-1265). Nothing else
  # about the fixture changes -- TYPE-D still has exactly one canonical member
  # and one marked one -- so `unlabeled_duplicate_pair` and
  # `no_canonical_designated` both stay silent. That is the whole point: no
  # count of canonical members can see a DIRECTION.
  #
  # The baseline projection carries no dependency edges at all, which is why
  # this guard cannot fire on any other case in this suite.
  awk -F'\t' 'BEGIN { OFS = "\t" } $3 == "T.d1" { $6 = "T.d2" } { print }' \
    "$dir/projection.tsv" > "$dir/p.tmp"
  mv "$dir/p.tmp" "$dir/projection.tsv"
  run_case "$dir"; expect_tag canonical-is-the-dependency "$dir" "CANONICAL-IS-NOT-THE-DEPENDENCY"
}

CASES=(
  case_baseline
  case_empty_projection
  case_below_floor
  case_unlabeled_duplicate_pair
  case_no_canonical_designated
  case_target_absent
  case_target_unsettled
  case_chain
  case_different_proposition
  case_shared_declaration_pair
  case_canonical_is_the_dependency
)

# Case name -> the mutation expected to kill it, and the anchor that mutation
# rewrites. Anchors are the guard's own rejection CONDITION; replacing it with
# `if False:` removes the rejection while leaving the scan (and therefore the
# scanned counts) intact.
MUTATION_NAMES=(
  identity_classes_empty
  identity_classes_below_floor
  unlabeled_duplicate_pair
  no_canonical_designated
  equivalent_to_target_absent
  equivalent_to_target_unsettled
  equivalent_to_chain
  equivalent_to_different_proposition
  shared_declaration_pair
  canonical_is_the_dependency
)
MUTATION_ANCHORS=(
  "    if len(classes) == 0:"
  "    if count < floor:"
  "        if len(canonical) > 1:"
  "        if len(canonical) == 0:"
  "        if target_is_absent:"
  "        if target_status not in SETTLED:"
  "        if target_eq:"
  "        if own_type != target_type:"
  "            if len(unmarked) > 1:"
  "                if other_name in reach.get(name, frozenset()):"
)
MUTATION_REPLACEMENTS=(
  "    if False:"
  "    if False:"
  "        if False:"
  "        if False:"
  "        if False:"
  "        if False:"
  "        if False:"
  "        if False:"
  "            if False:"
  "                if False:"
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
cp "$ROOT/scripts/check-trust-closure.py" "$WORK/scripts/"
cp "$ROOT/scripts/check-fact-depends-derived.py" "$WORK/scripts/"
cp "$SUBJECT" "$WORK/scripts/check-proposition-duplication.py"
SCRIPT="$WORK/scripts/check-proposition-duplication.py"

note "== baseline =="
run_all_cases base
BASE_PASS=$PASS
BASE_FAIL=$FAIL
if [ "$BASE_FAIL" -ne 0 ]; then
  note "PROPOSITION_DUPLICATION_CONTROLS|BASELINE FAILED: ${FAILED_NAMES[*]}"
  exit 1
fi
if [ "$BASE_PASS" -eq 0 ]; then
  note "PROPOSITION_DUPLICATION_CONTROLS|BASELINE ran ZERO cases -- that is a failure, not a pass"
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
note "PROPOSITION_DUPLICATION_CONTROLS|cases=${#CASES[@]}|mutations=${#MUTATION_NAMES[@]}|not_exactly_one=$MUT_FAIL"
if [ "$MUT_FAIL" -ne 0 ]; then
  exit 1
fi
exit 0
