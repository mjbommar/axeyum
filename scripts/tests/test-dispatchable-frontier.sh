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

ALL_GUARDS=(G1 G2 G3 G4 G5 G6 S1 S2 S3 S4 S5)

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

# --- the statable-here inputs ------------------------------------------------
# `Test.plain` is a kernel declaration; `Test.bridgeThing` is a Lean surface
# constant with no kernel counterpart, witnessed by the SETTLED mirror. `Eq` and
# `Nat` are S1's presence probes and every real environment has them.
env = {"schema_version": 1, "kind": "axeyum-kernel-environment-snapshot",
       "read_from": "fixture", "command": "fixture", "coverage": "fixture",
       "control": "fixture", "notes": "fixture",
       "declaration_count": 3,
       "declarations": ["Eq", "Nat", "Test.plain"]}
(d / "env.json").write_text(json.dumps(env, indent=1))

vocab = {"schema_version": 1,
         "kind": "axeyum-autogenesis-statable-vocabulary",
         "derivation": "fixture", "keyed_by": "source_name",
         "bridge": ["Test.bridgeThing"],
         "settled": [{"source_name": "Test.settled",
                      "constants": ["Test.bridgeThing", "Test.plain"]}]}
(d / "vocab.json").write_text(json.dumps(vocab, indent=1))

# The catalog is where source_name joins to fact_id -- the vocabulary never
# names a fact id, so that held-out ids cannot leak into a non-population file.
catalog = {"facts": [
    {"kind": "external-source", "source_name": "Test.blocked",
     "fact_id": "F:ml430-fix-blocked"},
    {"kind": "external-source", "source_name": "Test.codomain",
     "fact_id": "F:ml430-fix-codomain"},
    {"kind": "external-source", "source_name": "Test.settled",
     "fact_id": "F:ml430-fix-settled"},
    {"kind": "external-source", "source_name": "Test.dispatchable",
     "fact_id": "F:ml430-fix-dispatchable"},
]}
(d / "catalog.json").write_text(json.dumps(catalog, indent=1))

# An extension manifest with no held-out rows of its own: the fixture's split
# lives entirely in `nursery.json`, and this exercises the dual-manifest read.
extension = {"schema_version": 1,
             "kind": "axeyum-autogenesis-nursery-extension",
             "entries": []}
(d / "extension.json").write_text(json.dumps(extension, indent=1))
PY
}

edit() {
  # edit <fixture-dir> <python-snippet-on-stdin>
  python3 - "$1"
}

fixargs() {
  # Every input is REQUIRED by the script, so the fixtures must supply all of
  # them; a default that silently fell back to the real tree would make a case
  # pass for the wrong reason.
  printf '%s\n' --facts-dir "$1/facts" --nursery "$1/nursery.json" \
    --registry "$1/registry.json" --extension "$1/extension.json" \
    --env-snapshot "$1/env.json" --vocabulary "$1/vocab.json" \
    --catalog "$1/catalog.json"
}

BASE="$WORK/base"
mkfixture "$BASE"
mapfile -t ARGS_BASE < <(fixargs "$BASE")

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
mapfile -t A < <(fixargs "$G1")
run "G1-stale-registry-entry" 1 G1 -- "${A[@]}"

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
mapfile -t A < <(fixargs "$G2")
run "G2-unwitnessed-codomain-claim" 1 G2 -- "${A[@]}"

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
mapfile -t A < <(fixargs "$G2B")
run "G2-codomain-entry-without-witness-regex" 1 G2 -- "${A[@]}"

# ---- case G3: the registry blocks a mirror we already closed ----------------
G3="$WORK/g3"; cp -r "$BASE" "$G3"
python3 - "$G3" <<'PY'
import json, sys, pathlib
d = pathlib.Path(sys.argv[1])
p = d / "facts" / "F-ml430-fix-blocked.json"
f = json.loads(p.read_text())
f["epistemic_status"] = "proved"
p.write_text(json.dumps(f, indent=1))
# Closing a mirror puts it in the vocabulary's settled list too; without this
# the mutant would fire S4 as well and the case would stop isolating G3.
v = d / "vocab.json"
voc = json.loads(v.read_text())
voc["settled"].append({"source_name": "Test.blocked",
                       "constants": ["Test.plain"]})
v.write_text(json.dumps(voc, indent=1))
PY
mapfile -t A < <(fixargs "$G3")
run "G3-blocks-a-settled-mirror" 1 G3 -- "${A[@]}"

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
mapfile -t A < <(fixargs "$G4")
run "G4-empty-dispatchable-set" 1 G4 -- "${A[@]}"

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
mapfile -t A < <(fixargs "$G5")
run "G5-unbacked-divergence-claim" 1 G5 -- "${A[@]}"

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
mapfile -t A < <(fixargs "$G5B")
run "G5-non-codomain-entry-without-mathlib-source" 1 G5 -- "${A[@]}"

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

# ============================================================================
# The statable-here vocabulary. S1-S4 run on every default invocation; S5 is
# the screen.
# ============================================================================

# ---- case S1a: the snapshot's own count disagrees with its list -------------
S1A="$WORK/s1a"; cp -r "$BASE" "$S1A"
python3 - "$S1A/env.json" <<'PY'
import json, sys, pathlib
p = pathlib.Path(sys.argv[1]); d = json.loads(p.read_text())
d["declaration_count"] = 999
p.write_text(json.dumps(d, indent=1))
PY
mapfile -t A < <(fixargs "$S1A")
run "S1-snapshot-count-disagrees" 1 S1 -- "${A[@]}"

# ---- case S1b: a snapshot no kernel environment could produce ---------------
# Dropping `Nat` also drops nothing else the fixture needs, so this isolates the
# PRESENCE probe. Without it, an empty or truncated snapshot -- which rejects
# everything, so the screen looks strict -- reads as a working screen.
S1B="$WORK/s1b"; cp -r "$BASE" "$S1B"
python3 - "$S1B/env.json" <<'PY'
import json, sys, pathlib
p = pathlib.Path(sys.argv[1]); d = json.loads(p.read_text())
d["declarations"] = [n for n in d["declarations"] if n != "Nat"]
d["declaration_count"] = len(d["declarations"])
p.write_text(json.dumps(d, indent=1))
PY
mapfile -t A < <(fixargs "$S1B")
run "S1-snapshot-missing-a-universal-declaration" 1 S1 -- "${A[@]}"

# ---- case S1c: a snapshot that contains a name no kernel can declare --------
# The OTHER way a screen goes vacuous, and the dangerous one: it ADMITS
# everything rather than rejecting everything, so nothing downstream complains.
S1C="$WORK/s1c"; cp -r "$BASE" "$S1C"
python3 - "$S1C/env.json" <<'PY'
import json, sys, pathlib
p = pathlib.Path(sys.argv[1]); d = json.loads(p.read_text())
d["declarations"].append("axeyum probe no declaration can carry")
d["declaration_count"] = len(d["declarations"])
p.write_text(json.dumps(d, indent=1))
PY
mapfile -t A < <(fixargs "$S1C")
run "S1-snapshot-admits-everything" 1 S1 -- "${A[@]}"

# ---- case S2a: a bridge constant no settled mirror witnesses ----------------
S2A="$WORK/s2a"; cp -r "$BASE" "$S2A"
python3 - "$S2A/vocab.json" <<'PY'
import json, sys, pathlib
p = pathlib.Path(sys.argv[1]); d = json.loads(p.read_text())
d["bridge"].append("Test.neverWitnessed")
p.write_text(json.dumps(d, indent=1))
PY
mapfile -t A < <(fixargs "$S2A")
run "S2-unwitnessed-bridge-constant" 1 S2 -- "${A[@]}"

# ---- case S2b: a bridge entry for something the kernel already declares -----
# Not merely redundant: a bridge for a declared name hides a rename, so the
# screen keeps admitting a constant after the kernel stopped providing it.
S2B="$WORK/s2b"; cp -r "$BASE" "$S2B"
python3 - "$S2B/vocab.json" <<'PY'
import json, sys, pathlib
p = pathlib.Path(sys.argv[1]); d = json.loads(p.read_text())
d["bridge"].append("Test.plain")
p.write_text(json.dumps(d, indent=1))
PY
mapfile -t A < <(fixargs "$S2B")
run "S2-bridge-shadows-the-environment" 1 S2 -- "${A[@]}"

# ---- case S3: the screen rejects a mirror we already closed ----------------
# THE FALSE-POSITIVE CONTROL for the positive screen. Dropping the bridge entry
# leaves the settled mirror unstatable, which -- since we demonstrably closed it
# -- means the vocabulary is wrong, not the mirror.
S3="$WORK/s3"; cp -r "$BASE" "$S3"
python3 - "$S3/vocab.json" <<'PY'
import json, sys, pathlib
p = pathlib.Path(sys.argv[1]); d = json.loads(p.read_text())
d["bridge"] = []
p.write_text(json.dumps(d, indent=1))
PY
mapfile -t A < <(fixargs "$S3")
run "S3-screen-rejects-a-settled-mirror" 1 S3 -- "${A[@]}"

# ---- case S4a: a row listed as settled that the ledger says is open --------
# This is the attack S2 alone cannot see: adding a row promotes its constants
# into the bridge, so without S4 any constant can be made "witnessed" by
# listing an open proposition.
S4A="$WORK/s4a"; cp -r "$BASE" "$S4A"
python3 - "$S4A/vocab.json" <<'PY'
import json, sys, pathlib
p = pathlib.Path(sys.argv[1]); d = json.loads(p.read_text())
d["settled"].append({"source_name": "Test.dispatchable",
                     "constants": ["Test.plain"]})
p.write_text(json.dumps(d, indent=1))
PY
mapfile -t A < <(fixargs "$S4A")
run "S4-row-listed-settled-but-ledger-says-open" 1 S4 -- "${A[@]}"

# ---- case S4b: a settled mirror DROPPED from the vocabulary -----------------
# The other direction, and the one that defeats S3: narrow the population and
# the false-positive control passes over whatever is left. The bridge is emptied
# alongside so that this mutant fires S4 and nothing else -- which is exactly
# the shape a lane would produce while "tidying" a vocabulary it could not make
# pass.
S4B="$WORK/s4b"; cp -r "$BASE" "$S4B"
python3 - "$S4B/vocab.json" <<'PY'
import json, sys, pathlib
p = pathlib.Path(sys.argv[1]); d = json.loads(p.read_text())
d["settled"] = []
d["bridge"] = []
p.write_text(json.dumps(d, indent=1))
PY
mapfile -t A < <(fixargs "$S4B")
run "S4-settled-mirror-missing-from-vocabulary" 1 S4 -- "${A[@]}"

# ---- case S5: the positive screen rejects an unstatable candidate ----------
# `screened-ok` against the divergence registry is NOT sufficient: this
# candidate passes the registry cleanly and still cannot be stated here.
cat > "$WORK/candidates-unstatable.json" <<'JSON'
{"candidates": [
  {"name": "Test.over_a_missing_structure", "statement": "forall s, s.ok = s",
   "constants": ["Test.plain", "Std.PRange.Rco"]},
  {"name": "Test.fine", "statement": "forall n, n.plain = n",
   "constants": ["Test.plain", "Test.bridgeThing"]}
]}
JSON
run "S5-screen-rejects-unstatable-candidate" 1 S5 -- \
    --registry "$BASE/registry.json" --env-snapshot "$BASE/env.json" \
    --vocabulary "$BASE/vocab.json" \
    --statable "$WORK/candidates-unstatable.json"

# ---- case 0c: the positive screen's false-positive control -----------------
cat > "$WORK/candidates-statable.json" <<'JSON'
{"candidates": [
  {"name": "Test.fine", "statement": "forall n, n.plain = n",
   "constants": ["Test.plain", "Test.bridgeThing"]},
  {"name": "Test.also_fine", "statement": "forall n, n.plain n = n",
   "constants": ["Eq", "Nat"]}
]}
JSON
run "statable-screen-passes-clean-candidates" 0 NONE -- \
    --registry "$BASE/registry.json" --env-snapshot "$BASE/env.json" \
    --vocabulary "$BASE/vocab.json" \
    --statable "$WORK/candidates-statable.json"

# ---- case 0d: and it re-screens the REAL preregistered population -----------
# Not a fixture: `nursery-v2-extension.json` carries every entry's constants, so
# the preregistered rows are re-screened on every run rather than only at the
# moment they were written.
run "statable-screen-passes-the-real-extension" 0 NONE -- \
    --statable "$ROOT/artifacts/autogenesis/nursery-v2-extension.json"

# ---- a candidate with no constants cannot be decided, and must not pass -----
cat > "$WORK/candidates-no-constants.json" <<'JSON'
{"candidates": [{"name": "Test.undecidable", "statement": "forall n, n = n"}]}
JSON
run "statable-candidate-without-constants-is-exit-2" 2 NONE -- \
    --registry "$BASE/registry.json" --env-snapshot "$BASE/env.json" \
    --vocabulary "$BASE/vocab.json" \
    --statable "$WORK/candidates-no-constants.json"

# ---- input errors are exit 2, deliberately distinct from a guard failure ----
run "missing-registry-is-exit-2" 2 NONE -- --registry "$WORK/nope.json"
run "missing-extension-is-exit-2" 2 NONE -- --facts-dir "$BASE/facts" \
    --nursery "$BASE/nursery.json" --registry "$BASE/registry.json" \
    --extension "$WORK/nope.json" --env-snapshot "$BASE/env.json" \
    --vocabulary "$BASE/vocab.json" --catalog "$BASE/catalog.json"

echo
if [ "$FAILURES" -ne 0 ]; then
  echo "check-dispatchable-frontier controls: $FAILURES of $CASES case(s) FAILED"
  exit 1
fi
echo "check-dispatchable-frontier controls: all $CASES case(s) passed"
