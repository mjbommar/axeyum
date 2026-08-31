#!/usr/bin/env bash
# Guard-deletion kill table for scripts/check-structural-index.py
# (L3 phase D2, ADR-0905). Mirrors scripts/tests/test-graph-join-mutations.sh's
# method: guards are pure functions over already-loaded Python objects, so
# fixtures are small hand-built dicts (scripts/tests/structural_index_mutations.py)
# driven through a tiny Python harness against a SCRATCH COPY of
# check-structural-index.py and scripts/lib/structural_index.py -- never the
# tracked files.
#
# CLAUDE.md's standing rule: "when you touch a checker, delete one guard and
# require that EXACTLY ONE test dies." held_out_fact_ids() reads real nursery
# files, so this copies the two committed nursery files into the scratch
# tree (nothing else under artifacts/autogenesis/ is needed) so the
# HELD_OUT_EXCLUDED guard's fixture can use a REAL held-out fact_id rather
# than a fabricated one this checker's own logic would not actually reject
# for the reason the guard claims.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRATCH="$(mktemp -d "${TMPDIR:-/tmp}/si-mutation-XXXXXX")"
trap 'rm -rf "$SCRATCH"' EXIT

mkdir -p "$SCRATCH/scripts/lib" "$SCRATCH/scripts/tests" "$SCRATCH/artifacts/autogenesis"
cp "$REPO_ROOT/scripts/check-structural-index.py" "$SCRATCH/scripts/check-structural-index.py"
cp "$REPO_ROOT/scripts/lib/structural_index.py" "$SCRATCH/scripts/lib/structural_index.py"
cp "$REPO_ROOT/scripts/tests/structural_index_mutations.py" "$SCRATCH/scripts/tests/structural_index_mutations.py"
cp "$REPO_ROOT/artifacts/autogenesis/nursery-v1.json" "$SCRATCH/artifacts/autogenesis/nursery-v1.json"
cp "$REPO_ROOT/artifacts/autogenesis/nursery-v2-extension.json" "$SCRATCH/artifacts/autogenesis/nursery-v2-extension.json"

GUARDS=(EMPTY_INDEX FIXED_QUERIES HELD_OUT_EXCLUDED GOAL_FEATURE_NO_LEAK SIGNAL_SEPARATION ABSENCE_UNANSWERABLE)
declare -A STUB=(
  [EMPTY_INDEX]='def check_empty_index(records):\n    return []\n'
  [FIXED_QUERIES]='def check_fixed_queries(records, dep_index, queries):\n    return []\n'
  [HELD_OUT_EXCLUDED]='def check_held_out_excluded(features):\n    return []\n'
  [GOAL_FEATURE_NO_LEAK]='def check_goal_feature_no_leak(features):\n    return []\n'
  [SIGNAL_SEPARATION]='def check_signal_separation(records, dep_index, queries):\n    return []\n'
  [ABSENCE_UNANSWERABLE]='def check_absence_unanswerable(records, dep_index, queries):\n    return []\n'
)

clear_pycache() {
  find "$SCRATCH" -name '__pycache__' -exec rm -rf {} + 2>/dev/null || true
}

run_all_fixtures() {
  PYTHONPATH="$SCRATCH/scripts:$SCRATCH/scripts/lib:$SCRATCH/scripts/tests" /usr/bin/python3 - "$SCRATCH" <<'PYEOF'
import importlib.util
import sys

scratch = sys.argv[1]

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod

si = load("structural_index", f"{scratch}/scripts/lib/structural_index.py")
fx = load("structural_index_mutations", f"{scratch}/scripts/tests/structural_index_mutations.py")
csi = load("check_structural_index", f"{scratch}/scripts/check-structural-index.py")

results = {}

good_records = fx.good_records()
good_dep_index = si.build_dependency_index(good_records)
good_queries = fx.good_queries()
good_features = fx.good_features()

results["good"] = (
    csi.check_empty_index(good_records)
    + csi.check_fixed_queries(good_records, good_dep_index, good_queries)
    + csi.check_held_out_excluded(good_features)
    + csi.check_goal_feature_no_leak(good_features)
    + csi.check_signal_separation(good_records, good_dep_index, good_queries)
    + csi.check_absence_unanswerable(good_records, good_dep_index, good_queries)
)

results["bad_EMPTY_INDEX"] = csi.check_empty_index(fx.bad_empty_index_records())
results["bad_FIXED_QUERIES"] = csi.check_fixed_queries(
    good_records, good_dep_index, fx.bad_fixed_queries()
)

held_out = si.held_out_fact_ids()
assert held_out, "fixture setup: no held-out fact_id found in copied nursery files"
one_held_out = sorted(held_out)[0]
results["bad_HELD_OUT_EXCLUDED"] = csi.check_held_out_excluded(
    fx.bad_held_out_features(one_held_out)
)

results["bad_GOAL_FEATURE_NO_LEAK"] = csi.check_goal_feature_no_leak(
    fx.bad_goal_feature_leak_features()
)
results["bad_SIGNAL_SEPARATION"] = csi.check_signal_separation(
    good_records, good_dep_index, fx.bad_signal_separation_queries()
)
results["bad_ABSENCE_UNANSWERABLE"] = csi.check_absence_unanswerable(
    good_records, good_dep_index, fx.bad_absence_unanswerable_queries()
)

for name, problems in results.items():
    print(f"{name}={'FAIL' if problems else 'PASS'}")
PYEOF
}

echo "== baseline (unmutated) =="
clear_pycache
baseline="$(run_all_fixtures)"
echo "$baseline"

echo "$baseline" | grep -qx 'good=PASS' || {
  echo "FAIL: good fixture does not pass the unmutated checker" >&2
  exit 1
}
for guard in "${GUARDS[@]}"; do
  echo "$baseline" | grep -qx "bad_${guard}=FAIL" || {
    echo "FAIL: bad_${guard} does not fail the unmutated checker" >&2
    exit 1
  }
done

FAILURES=0
for guard in "${GUARDS[@]}"; do
  echo "== mutating ${guard} (stub returns []) =="
  cp "$REPO_ROOT/scripts/check-structural-index.py" "$SCRATCH/scripts/check-structural-index.py"
  python3 - "$SCRATCH/scripts/check-structural-index.py" "$guard" "${STUB[$guard]}" <<'PYEOF'
import re
import sys

path, guard, stub = sys.argv[1], sys.argv[2], sys.argv[3]
stub = stub.replace("\\n", "\n")
text = open(path, encoding="utf-8").read()
marker = f"# GUARD:{guard}\n"
start = text.index(marker) + len(marker)
# The function body runs until the next "\n\n\n" or next "# GUARD:" marker /
# next top-level "def " at column 0, whichever comes first after `start`.
rest = text[start:]
end_candidates = []
m = re.search(r"\n# GUARD:", rest)
if m:
    end_candidates.append(m.start())
m2 = re.search(r"\ndef ", rest)
if m2:
    end_candidates.append(m2.start())
end = min(end_candidates) if end_candidates else len(rest)
new_text = text[:start] + stub + "\n\n" + rest[end:].lstrip("\n")
open(path, "w", encoding="utf-8").write(new_text)
PYEOF
  clear_pycache
  mutated="$(run_all_fixtures)"
  echo "$mutated"

  ok=1
  for other in "${GUARDS[@]}"; do
    if [ "$other" = "$guard" ]; then
      echo "$mutated" | grep -qx "bad_${other}=PASS" || {
        echo "FAIL: mutating ${guard} did not flip bad_${other} to PASS" >&2
        ok=0
      }
    else
      echo "$mutated" | grep -qx "bad_${other}=FAIL" || {
        echo "FAIL: mutating ${guard} also flipped bad_${other} (should stay FAIL)" >&2
        ok=0
      }
    fi
  done
  echo "$mutated" | grep -qx 'good=PASS' || {
    echo "FAIL: mutating ${guard} broke the good fixture" >&2
    ok=0
  }
  if [ "$ok" -eq 1 ]; then
    echo "KILL_TABLE|guard=${guard}|result=killed-exactly-its-own-mutation"
  else
    FAILURES=$((FAILURES + 1))
  fi
done

if [ "$FAILURES" -gt 0 ]; then
  echo "test-structural-index-mutations: ${FAILURES} guard(s) not killed 1:1" >&2
  exit 1
fi

echo "test-structural-index-mutations: all ${#GUARDS[@]} guards killed 1:1"
