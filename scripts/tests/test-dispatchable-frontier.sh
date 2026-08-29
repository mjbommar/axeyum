#!/usr/bin/env bash
# Controls for scripts/check-dispatchable-frontier.py.
#
# One case per guard, and each case asserts BOTH that its own guard fired AND
# that no other guard fired -- so a guard that is deleted or weakened is killed
# by exactly one case, and a guard that over-fires is killed by every other
# case. The fixtures are synthetic and live in a scratch directory; nothing here
# mutates a tracked source file (a mutated constant on disk is indistinguishable
# from a wrong one to any other lane compiling from the same tree).
#
# Case 0 is the FALSE-POSITIVE control and it runs twice: once on a healthy
# synthetic fixture and once on the REAL repository tree. A gate that fires on
# healthy input gets ignored, which is the same end state as no gate.

set -u -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRIPT="$ROOT/scripts/check-dispatchable-frontier.py"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

FAILURES=0
CASES=0

ALL_GUARDS=(G1 G2 G3 G4 G5 G6)

# run <label> <expected-exit> <expected-guard-or-NONE> -- <args...>
run() {
  local label="$1" want_exit="$2" want_guard="$3"; shift 3
  [ "$1" = "--" ] && shift
  CASES=$((CASES + 1))
  local out status
  out="$(python3 "$SCRIPT" "$@" 2>&1)"
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
    FAILURES=$((FAILURES + 1))
    echo "--- output [$label] ---"
    printf '%s\n' "$out" | sed 's/^/    /'
    echo "--- end ---"
  else
    echo "ok   [$label]"
  fi
}

# ---------------------------------------------------------------- fixtures ---
mkfixture() {
  # mkfixture <dir> ; builds a HEALTHY fixture: one blocked mirror, one
  # witnessed codomain mirror, one settled mirror, one dispatchable mirror.
  local d="$1"
  mkdir -p "$d/facts"
  python3 - "$d" "$ROOT" <<'PY'
import json, pathlib, sys
d = pathlib.Path(sys.argv[1]); root = sys.argv[2]

def fact(ident, status, statement):
    return {
        "schema_version": 1, "id": ident, "title": ident,
        "statement": ident,
        "formal": {"language": "lean4-surface", "statement": statement,
                   "fragment": "Nat"},
        "epistemic_status": status, "depends_on": [], "evidence": [],
        "provenance": {"date": "2026-08-29", "established_by": "fixture",
                       "source": "fixture"},
    }

facts = [
    fact("F:ml430-fix-blocked", "open", "forall n, n.divergesHere = 1"),
    fact("F:ml430-fix-codomain", "open", "forall n i, n.boolishHere i = false"),
    fact("F:ml430-fix-settled", "proved", "forall n, n.plain = 1"),
    fact("F:ml430-fix-dispatchable", "open", "forall n, n.plain n = n"),
    fact("F:ml430-mutation-fix", "open", "forall n, n.plain = 2"),
]
for f in facts:
    (d / "facts" / (f["id"].replace(":", "-").replace("F-", "F-") + ".json")
     ).write_text(json.dumps(f, indent=1))

nursery = {"entries": [
    {"fact_id": "F:ml430-fix-blocked", "partition": "train", "mutation_of": None},
    {"fact_id": "F:ml430-fix-codomain", "partition": "train", "mutation_of": None},
    {"fact_id": "F:ml430-fix-settled", "partition": "train", "mutation_of": None},
    {"fact_id": "F:ml430-fix-dispatchable", "partition": "development",
     "mutation_of": None},
    {"fact_id": "F:ml430-mutation-fix", "partition": "train",
     "mutation_of": "F:ml430-fix-settled"},
]}
(d / "nursery.json").write_text(json.dumps(nursery, indent=1))

registry = {"schema_version": 1,
            "kind": "axeyum-autogenesis-mirror-divergence-registry",
            "constructions": [
    {"mathlib_constant": "Test.divergesHere",
     "surface_forms": ["divergesHere"], "class": "definitional",
     "why": "fixture",
     "mathlib_source": {"path": "Fixture/Nowhere.lean"},
     "recorded_in": "artifacts/autogenesis/mirror-divergence-registry.json"},
    {"mathlib_constant": "Test.boolishHere",
     "surface_forms": ["boolishHere"], "class": "codomain",
     "mathlib_codomain": "Bool", "axeyum_codomain": "Nat",
     "codomain_witness_regex": "boolishHere[^=]*=\\s*(true|false)\\b",
     "why": "fixture"},
]}
(d / "registry.json").write_text(json.dumps(registry, indent=1))
PY
}

edit() {
  # edit <fixture-dir> <python-snippet-on-stdin>
  python3 - "$1"
}

BASE="$WORK/base"
mkfixture "$BASE"
ARGS_BASE=(--facts-dir "$BASE/facts" --nursery "$BASE/nursery.json"
           --registry "$BASE/registry.json")

# ---- case 0: FALSE-POSITIVE controls -- healthy input must be silent -------
run "healthy-fixture-passes" 0 NONE -- "${ARGS_BASE[@]}"
run "healthy-real-tree-passes" 0 NONE --

# ---- case G1: a registry entry that matches no proposition ------------------
G1="$WORK/g1"; cp -r "$BASE" "$G1"
python3 - "$G1/registry.json" <<'PY'
import json, sys, pathlib
p = pathlib.Path(sys.argv[1]); d = json.loads(p.read_text())
d["constructions"].append({
    "mathlib_constant": "Test.neverMentioned",
    "surface_forms": ["zzzNotInAnyStatement"], "class": "algorithmic",
    "why": "mutant", "mathlib_source": {"path": "Fixture/Nowhere.lean"},
    "recorded_in": "artifacts/autogenesis/mirror-divergence-registry.json"})
p.write_text(json.dumps(d, indent=1))
PY
run "G1-stale-registry-entry" 1 G1 -- --facts-dir "$G1/facts" \
    --nursery "$G1/nursery.json" --registry "$G1/registry.json"

# ---- case G2: a codomain claim nothing in the pinned source witnesses -------
G2="$WORK/g2"; cp -r "$BASE" "$G2"
python3 - "$G2/facts" <<'PY'
import json, sys, pathlib
d = pathlib.Path(sys.argv[1])
p = d / "F-ml430-fix-codomain.json"
f = json.loads(p.read_text())
# same construction, but no `true`/`false` literal anywhere: the codomain claim
# is now an assertion nobody can re-derive from the pinned statements.
f["formal"]["statement"] = "forall n i, n.boolishHere i = n.other i"
p.write_text(json.dumps(f, indent=1))
PY
run "G2-unwitnessed-codomain-claim" 1 G2 -- --facts-dir "$G2/facts" \
    --nursery "$G2/nursery.json" --registry "$G2/registry.json"

# ---- case G2b: a codomain entry that carries no witness regex at all --------
# Found by mutation testing: without this case the "no regex" branch of G2 was
# deletable with every other case still green -- i.e. a `codomain` row could be
# added with nothing to re-derive it from, which is the exact failure G2 exists
# to prevent.
G2B="$WORK/g2b"; cp -r "$BASE" "$G2B"
python3 - "$G2B/registry.json" <<'PY'
import json, sys, pathlib
p = pathlib.Path(sys.argv[1]); d = json.loads(p.read_text())
for e in d["constructions"]:
    if e["class"] == "codomain":
        e.pop("codomain_witness_regex", None)
p.write_text(json.dumps(d, indent=1))
PY
run "G2-codomain-entry-without-witness-regex" 1 G2 -- --facts-dir "$G2B/facts" \
    --nursery "$G2B/nursery.json" --registry "$G2B/registry.json"

# ---- case G3: the registry blocks a mirror we already closed ----------------
G3="$WORK/g3"; cp -r "$BASE" "$G3"
python3 - "$G3/facts" <<'PY'
import json, sys, pathlib
d = pathlib.Path(sys.argv[1])
p = d / "F-ml430-fix-blocked.json"
f = json.loads(p.read_text())
f["epistemic_status"] = "proved"
p.write_text(json.dumps(f, indent=1))
PY
run "G3-blocks-a-settled-mirror" 1 G3 -- --facts-dir "$G3/facts" \
    --nursery "$G3/nursery.json" --registry "$G3/registry.json"

# ---- case G4: the dispatchable set is empty ---------------------------------
G4="$WORK/g4"; cp -r "$BASE" "$G4"
python3 - "$G4/nursery.json" <<'PY'
import json, sys, pathlib
p = pathlib.Path(sys.argv[1]); d = json.loads(p.read_text())
for e in d["entries"]:
    if e["fact_id"] == "F:ml430-fix-dispatchable":
        e["partition"] = "held-out"
p.write_text(json.dumps(d, indent=1))
PY
run "G4-empty-dispatchable-set" 1 G4 -- --facts-dir "$G4/facts" \
    --nursery "$G4/nursery.json" --registry "$G4/registry.json"

# ---- case G5: a non-re-derivable class with no recorded reading -------------
G5="$WORK/g5"; cp -r "$BASE" "$G5"
python3 - "$G5/registry.json" <<'PY'
import json, sys, pathlib
p = pathlib.Path(sys.argv[1]); d = json.loads(p.read_text())
for e in d["constructions"]:
    if e["class"] == "definitional":
        e.pop("recorded_in", None)
p.write_text(json.dumps(d, indent=1))
PY
run "G5-unbacked-divergence-claim" 1 G5 -- --facts-dir "$G5/facts" \
    --nursery "$G5/nursery.json" --registry "$G5/registry.json"

# ---- case G5b: a non-re-derivable class naming no Mathlib source ------------
# Also found by mutation testing: the `mathlib_source.path` branch of G5 had no
# case, so a definitional/algorithmic/recursion-principle blocker could be
# asserted with no source to check it against.
G5B="$WORK/g5b"; cp -r "$BASE" "$G5B"
python3 - "$G5B/registry.json" <<'PY'
import json, sys, pathlib
p = pathlib.Path(sys.argv[1]); d = json.loads(p.read_text())
for e in d["constructions"]:
    if e["class"] == "definitional":
        e.pop("mathlib_source", None)
p.write_text(json.dumps(d, indent=1))
PY
run "G5-non-codomain-entry-without-mathlib-source" 1 G5 -- \
    --facts-dir "$G5B/facts" --nursery "$G5B/nursery.json" \
    --registry "$G5B/registry.json"

# ---- case G6: the pre-preregistration screen rejects a diverging candidate --
cat > "$WORK/candidates-bad.json" <<'JSON'
{"candidates": [
  {"name": "Test.thing_divergesHere", "statement": "forall n, n.divergesHere = n"},
  {"name": "Test.thing_ok", "statement": "forall n, n.plain = n"}
]}
JSON
run "G6-screen-blocks-diverging-candidate" 1 G6 -- \
    --registry "$BASE/registry.json" --screen "$WORK/candidates-bad.json"

# ---- case 0b: the screen's own false-positive control -----------------------
cat > "$WORK/candidates-ok.json" <<'JSON'
{"candidates": [
  {"name": "Test.thing_ok", "statement": "forall n, n.plain = n"},
  {"name": "Test.other_ok", "statement": "forall n m, n.plain m = m"}
]}
JSON
run "screen-passes-clean-candidates" 0 NONE -- \
    --registry "$BASE/registry.json" --screen "$WORK/candidates-ok.json"

# ---- input errors are exit 2, deliberately distinct from a guard failure ----
run "missing-registry-is-exit-2" 2 NONE -- --registry "$WORK/nope.json"

echo
if [ "$FAILURES" -ne 0 ]; then
  echo "check-dispatchable-frontier controls: $FAILURES of $CASES case(s) FAILED"
  exit 1
fi
echo "check-dispatchable-frontier controls: all $CASES case(s) passed"
