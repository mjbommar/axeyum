#!/usr/bin/env bash
# Controls for `scripts/annotate-trust-closure-kernel-theorem.py`.
#
# The tool recovers a trust-closure `unresolved` fact's `formal.kernel_theorem`
# from what its own evidence already spells, in priority order: (1) the
# `ml430` mirror title "Mathlib v4.30 source proposition <Name>", (2) an
# unambiguous evidence `id` beginning `kernel-<Name>`, (3) an exact
# `formal.statement` == declaration `canonical_type` match (any kind, for a
# fact whose subject is a Definition rather than a Theorem). It deliberately
# does NOT fall back to scanning the whole fact's text for any mentioned
# theorem name -- measured against the real ledger, that scan picks up
# dependency theorems named in `supports`/`notes` prose and reports the WRONG
# subject. This suite's job is to keep that boundary in place: each fixture
# below is a case the tool must resolve, or must NOT resolve, and a mutation
# that blurs the boundary must fail exactly one of them.
#
#   bash scripts/tests/test-annotate-trust-closure-kernel-theorem.sh
#
# Exit 0 when every case behaves and every mutation kills exactly one.

set -u -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SUBJECT="$ROOT/scripts/annotate-trust-closure-kernel-theorem.py"
LANE="${AXEYUM_AGENT:-unowned}"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/annotate-trust-closure-controls-$LANE-XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

PASS=0
FAIL=0
FAILED_NAMES=()

note() { printf '%s\n' "$*"; }

# ---------------------------------------------------------------------------
# Fixtures: a five-declaration projection and six facts, one per case.
# ---------------------------------------------------------------------------
write_projection() {
  printf '%s\n' \
    "fx	theorem	T.by_title	0				TYPE-A" \
    "fx	theorem	T.by_id	0				TYPE-B" \
    "fx	definition	T.by_type	0				TYPE-C" \
    "fx	theorem	T.dep_only	0				TYPE-D" \
    "fx	theorem	T.ambiguous_a	0				TYPE-E" \
    "fx	theorem	T.ambiguous_b	0				TYPE-F" \
    > "$1"
}

write_facts() {
  mkdir -p "$1"

  # Case 1: title-resolvable (ml430 mirror shape).
  cat > "$1/F-case-title.json" <<'JSON'
{
  "id": "F:case-title",
  "title": "Mathlib v4.30 source proposition T.by_title",
  "proof_route": "kernel-lean",
  "epistemic_status": "proved",
  "formal": { "language": "lean4-surface", "statement": "irrelevant" },
  "depends_on": [],
  "evidence": [{ "id": "receipt-1", "check_status": "checked", "checker_command": "true" }]
}
JSON

  # Case 2: evidence-id resolvable (single "kernel-<Name>" prefix).
  cat > "$1/F-case-id.json" <<'JSON'
{
  "id": "F:case-id",
  "title": "some fact about T.by_id",
  "proof_route": "kernel-lean",
  "epistemic_status": "proved",
  "formal": { "language": "lean4", "statement": "irrelevant" },
  "depends_on": [],
  "evidence": [
    { "id": "kernel-T.by_id", "check_status": "checked", "checker_command": "true" },
    { "id": "footprint-T.by_id", "check_status": "checked", "checker_command": "true" }
  ]
}
JSON

  # Case 3: type-match resolvable (a Definition, not a Theorem -- neither
  # earlier tier can see it, only the exact canonical_type match can).
  cat > "$1/F-case-type.json" <<'JSON'
{
  "id": "F:case-type",
  "title": "a definition fact",
  "proof_route": "kernel-lean",
  "epistemic_status": "proved",
  "formal": { "language": "lean4", "statement": "def T.by_type : TYPE-C" },
  "depends_on": [],
  "evidence": [{ "id": "receipt-3", "check_status": "checked", "checker_command": "true" }]
}
JSON

  # Case 4: NEGATIVE control. T.dep_only is mentioned only in prose (as a
  # dependency), never as a title mirror, an evidence id, or the fact's own
  # statement. Must stay unresolved -- this is the exact shape that made an
  # earlier full-text-scan draft mis-annotate real facts in the ledger.
  cat > "$1/F-case-dep-only.json" <<'JSON'
{
  "id": "F:case-dep-only",
  "title": "a fact whose proof uses T.dep_only as a helper",
  "proof_route": "kernel-lean",
  "epistemic_status": "proved",
  "formal": { "language": "lean4", "statement": "irrelevant, and does not match T.dep_only" },
  "depends_on": [],
  "evidence": [
    {
      "id": "receipt-4",
      "check_status": "checked",
      "checker_command": "true",
      "supports": "rests on T.dep_only among other lemmas"
    }
  ]
}
JSON

  # Case 5: NEGATIVE control. Two "kernel-<Name>" evidence ids naming two
  # DIFFERENT existing theorems -- genuinely ambiguous, must stay unresolved.
  cat > "$1/F-case-ambiguous.json" <<'JSON'
{
  "id": "F:case-ambiguous",
  "title": "an umbrella fact bundling two theorems",
  "proof_route": "kernel-lean",
  "epistemic_status": "proved",
  "formal": { "language": "lean4", "statement": "irrelevant" },
  "depends_on": [],
  "evidence": [
    { "id": "kernel-T.ambiguous_a", "check_status": "checked", "checker_command": "true" },
    { "id": "kernel-T.ambiguous_b", "check_status": "checked", "checker_command": "true" }
  ]
}
JSON

  # Case 6: NEGATIVE control. Explicit `formal.kernel_theorem: null` -- the
  # deliberate shape. Must be left alone (not touched, not reported).
  cat > "$1/F-case-deliberate-null.json" <<'JSON'
{
  "id": "F:case-deliberate-null",
  "title": "a genuinely multi-theorem package",
  "proof_route": "kernel-lean",
  "epistemic_status": "proved",
  "formal": { "language": "lean4", "statement": "irrelevant", "kernel_theorem": null },
  "depends_on": [],
  "evidence": [{ "id": "receipt-6", "check_status": "checked", "checker_command": "true" }]
}
JSON
}

run_check() {
  local facts_dir="$1" proj="$2"
  python3 "$SUBJECT" --check --facts "$facts_dir" --projection "$proj"
}

check_case() {
  local name="$1" want_status="$2"
  shift 2
  local out status
  out="$("$@" 2>&1)"
  status=$?
  if [ "$status" != "$want_status" ]; then
    note "FAIL $name: exit=$status want=$want_status"
    note "  output: $out"
    FAIL=$((FAIL + 1))
    FAILED_NAMES+=("$name")
    return 1
  fi
  printf '%s' "$out"
  return 0
}

# ---------------------------------------------------------------------------
# Baseline: --check must find exactly 3 recoverable candidates (title, id,
# type), exit 1, and must NOT list any of the three negative-control cases.
# ---------------------------------------------------------------------------
FACTS="$WORK/facts"
PROJ="$WORK/projection.tsv"
write_projection "$PROJ"
write_facts "$FACTS"

OUT="$(run_check "$FACTS" "$PROJ" 2>&1)"
STATUS=$?

case_pass() {
  local name="$1"
  PASS=$((PASS + 1))
  note "PASS $name"
}
case_fail() {
  local name="$1" detail="$2"
  FAIL=$((FAIL + 1))
  FAILED_NAMES+=("$name")
  note "FAIL $name: $detail"
}

if [ "$STATUS" != "1" ]; then
  case_fail baseline_exit_status "expected exit 1 (candidates found), got $STATUS"
else
  case_pass baseline_exit_status
fi

if printf '%s' "$OUT" | grep -qF 'F:case-title -> T.by_title'; then
  case_pass resolves_by_title
else
  case_fail resolves_by_title "missing from: $OUT"
fi

if printf '%s' "$OUT" | grep -qF 'F:case-id -> T.by_id'; then
  case_pass resolves_by_evidence_id
else
  case_fail resolves_by_evidence_id "missing from: $OUT"
fi

if printf '%s' "$OUT" | grep -qF 'F:case-type -> T.by_type'; then
  case_pass resolves_by_type_match
else
  case_fail resolves_by_type_match "missing from: $OUT"
fi

if printf '%s' "$OUT" | grep -qF 'F:case-dep-only'; then
  case_fail rejects_dependency_only_mention "wrongly listed as recoverable: $OUT"
else
  case_pass rejects_dependency_only_mention
fi

if printf '%s' "$OUT" | grep -qF 'F:case-ambiguous'; then
  case_fail rejects_ambiguous_evidence_ids "wrongly listed as recoverable: $OUT"
else
  case_pass rejects_ambiguous_evidence_ids
fi

if printf '%s' "$OUT" | grep -qF 'F:case-deliberate-null'; then
  case_fail leaves_deliberate_null_alone "wrongly listed as recoverable: $OUT"
else
  case_pass leaves_deliberate_null_alone
fi

# ---------------------------------------------------------------------------
# --apply then --check again: must exit 0 (nothing left to do), and the
# deliberate-null fact's formal.kernel_theorem must still be exactly `null`
# (not overwritten, not deleted).
# ---------------------------------------------------------------------------
APPLY_OUT="$(python3 "$SUBJECT" --apply --facts "$FACTS" --projection "$PROJ" 2>&1)"
APPLY_STATUS=$?
if [ "$APPLY_STATUS" != "0" ]; then
  case_fail apply_exit_status "expected 0, got $APPLY_STATUS: $APPLY_OUT"
else
  case_pass apply_exit_status
fi

RECHECK_OUT="$(run_check "$FACTS" "$PROJ" 2>&1)"
RECHECK_STATUS=$?
if [ "$RECHECK_STATUS" != "0" ]; then
  case_fail recheck_after_apply_is_clean "expected 0, got $RECHECK_STATUS: $RECHECK_OUT"
else
  case_pass recheck_after_apply_is_clean
fi

NULL_VAL="$(python3 -c "import json; print(json.load(open('$FACTS/F-case-deliberate-null.json'))['formal']['kernel_theorem'])")"
if [ "$NULL_VAL" = "None" ]; then
  case_pass deliberate_null_untouched
else
  case_fail deliberate_null_untouched "kernel_theorem became: $NULL_VAL"
fi

# ---------------------------------------------------------------------------
# Mutation: delete the evidence-id tier and require that exactly ONE case
# (resolves_by_evidence_id) dies, applied in a scratch copy of the script --
# never the shared checkout (see test-trust-closure.sh's header for why).
# ---------------------------------------------------------------------------
# The subject does `ROOT = pathlib.Path(__file__).resolve().parents[1]` and
# then loads `ROOT/scripts/check-trust-closure.py` and
# `ROOT/scripts/check-fact-depends-derived.py` by path, so a mutant copy MUST
# sit in a `scripts/` directory carrying those two siblings too, or ROOT
# resolves to the scratch root and both imports fail with FileNotFoundError
# -- which looks like "every case died" and is not a targeted kill at all.
MUT_DIR="$WORK/mutant/scripts"
mkdir -p "$MUT_DIR"
cp "$ROOT/scripts/check-trust-closure.py" "$MUT_DIR/"
cp "$ROOT/scripts/check-fact-depends-derived.py" "$MUT_DIR/"
cp "$SUBJECT" "$MUT_DIR/annotate-trust-closure-kernel-theorem.py"
python3 - "$MUT_DIR/annotate-trust-closure-kernel-theorem.py" <<'PY'
import sys
path = sys.argv[1]
text = open(path).read()
marker = "    if len(id_cands) == 1:\n        return next(iter(id_cands))"
replacement = "    if False:\n        return next(iter(id_cands))"
assert marker in text, "evidence-id tier marker not found -- script shape changed"
open(path, "w").write(text.replace(marker, replacement, 1))
PY
find "$WORK" -name __pycache__ -exec rm -rf {} + 2>/dev/null

FACTS2="$WORK/facts2"
write_facts "$FACTS2"
MUT_OUT="$(python3 "$MUT_DIR/annotate-trust-closure-kernel-theorem.py" --check --facts "$FACTS2" --projection "$PROJ" 2>&1)"

MUT_KILLS=0
MUT_KILL_NAMES=()
if ! printf '%s' "$MUT_OUT" | grep -qF 'F:case-id -> T.by_id'; then
  MUT_KILLS=$((MUT_KILLS + 1)); MUT_KILL_NAMES+=("resolves_by_evidence_id")
fi
if ! printf '%s' "$MUT_OUT" | grep -qF 'F:case-title -> T.by_title'; then
  MUT_KILLS=$((MUT_KILLS + 1)); MUT_KILL_NAMES+=("resolves_by_title")
fi
if ! printf '%s' "$MUT_OUT" | grep -qF 'F:case-type -> T.by_type'; then
  MUT_KILLS=$((MUT_KILLS + 1)); MUT_KILL_NAMES+=("resolves_by_type_match")
fi

if [ "$MUT_KILLS" = "1" ] && [ "${MUT_KILL_NAMES[0]}" = "resolves_by_evidence_id" ]; then
  case_pass mutation_evidence_id_tier_kills_exactly_one
else
  case_fail mutation_evidence_id_tier_kills_exactly_one \
    "killed ${MUT_KILLS} case(s): ${MUT_KILL_NAMES[*]:-none}"
fi

# ---------------------------------------------------------------------------
note ""
note "PASS=$PASS FAIL=$FAIL"
if [ "$FAIL" -ne 0 ]; then
  note "failed: ${FAILED_NAMES[*]}"
  exit 1
fi
exit 0
