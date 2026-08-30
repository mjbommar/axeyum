#!/usr/bin/env bash
# Guard-deletion kill table for scripts/check-infrastructure-frontier.py
# (L2 phase G3, ADR-0845). Mirrors scripts/tests/test-graph-join-mutations.sh's
# method: check-infrastructure-frontier.py's guards are pure functions over
# already-loaded dicts/strings (or, for MISSING_JOIN, a filesystem path), so
# fixtures are the small hand-built values in
# scripts/tests/infrastructure_frontier_mutations.py, driven through a tiny
# Python harness rather than the CLI directly.
#
# CLAUDE.md's standing rule: "when you touch a checker, delete one guard and
# require that EXACTLY ONE test dies." This builds one Python driver per
# guard fixture, then -- in a SCRATCH COPY of check-infrastructure-frontier.py
# (never the tracked file) -- neuters exactly one guard at a time and
# re-runs every fixture through the mutated copy.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRATCH="$(mktemp -d "${TMPDIR:-/tmp}/if-mutation-XXXXXX")"
trap 'rm -rf "$SCRATCH"' EXIT

mkdir -p "$SCRATCH/scripts/lib" "$SCRATCH/scripts/tests"
cp "$REPO_ROOT/scripts/check-infrastructure-frontier.py" "$SCRATCH/scripts/check-infrastructure-frontier.py"
cp "$REPO_ROOT/scripts/gen-infrastructure-frontier.py" "$SCRATCH/scripts/gen-infrastructure-frontier.py"
cp "$REPO_ROOT/scripts/lib/infrastructure_frontier.py" "$SCRATCH/scripts/lib/infrastructure_frontier.py"
cp "$REPO_ROOT/scripts/tests/infrastructure_frontier_mutations.py" "$SCRATCH/scripts/tests/infrastructure_frontier_mutations.py"

GUARDS=(MISSING_JOIN STALE_ARTIFACT ROW_ID_UNIQUE ROW_ID_PURITY EMPTY_QUEUE_REASON ROW_EVIDENCE_COMPLETE METRIC_EXPECTATION CROSS_CHECK_PRESENT)
declare -A STUB=(
  [MISSING_JOIN]='def check_missing_join(join_path):\n    return []\n'
  [STALE_ARTIFACT]='def check_stale_artifact(committed_json, fresh_json, committed_md, fresh_md):\n    return []\n'
  [ROW_ID_UNIQUE]='def check_row_id_unique(frontier):\n    return []\n'
  [ROW_ID_PURITY]='def check_row_id_purity(frontier):\n    return []\n'
  [EMPTY_QUEUE_REASON]='def check_empty_queue_reason(frontier):\n    return []\n'
  [ROW_EVIDENCE_COMPLETE]='def check_row_evidence_complete(frontier):\n    return []\n'
  [METRIC_EXPECTATION]='def check_metric_expectation(frontier):\n    return []\n'
  [CROSS_CHECK_PRESENT]='def check_cross_check_present(frontier):\n    return []\n'
)

clear_pycache() {
  find "$SCRATCH" -name '__pycache__' -exec rm -rf {} + 2>/dev/null || true
}

# Runs every fixture's guard call through the (possibly mutated) checker in
# $SCRATCH, printing "<fixture>=PASS" (guard returned []) or "<fixture>=FAIL"
# (guard returned a non-empty list). "good" must always PASS every guard;
# "bad_<GUARD>" must FAIL only guard <GUARD> in the baseline, and flip to
# PASS only when THAT guard is deleted.
run_all_fixtures() {
  PYTHONPATH="$SCRATCH/scripts:$SCRATCH/scripts/lib:$SCRATCH/scripts/tests" /usr/bin/python3 - "$SCRATCH" <<'PYEOF'
import importlib.util
import json
import sys
from pathlib import Path

scratch = Path(sys.argv[1])

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod

inf = load("infrastructure_frontier", scratch / "scripts/lib/infrastructure_frontier.py")
fx = load("infrastructure_frontier_mutations", scratch / "scripts/tests/infrastructure_frontier_mutations.py")
cif = load("check_infrastructure_frontier", scratch / "scripts/check-infrastructure-frontier.py")

good_join_path = scratch / "fixture-join" / "good.join.json"
missing_join_path = scratch / "fixture-join" / "does-not-exist.join.json"
empty_dims_join_path = scratch / "fixture-join" / "empty-dims.join.json"
fx.write_join(good_join_path)
fx.write_join(empty_dims_join_path, fx.bad_empty_join_dict())

good_committed_json = "SAME"
good_committed_md = "SAME MD"

results = {}

results["good"] = (
    cif.check_missing_join(good_join_path)
    + cif.check_stale_artifact(good_committed_json, good_committed_json, good_committed_md, good_committed_md)
    + cif.check_row_id_unique(fx.good_frontier())
    + cif.check_row_id_purity(fx.good_frontier())
    + cif.check_empty_queue_reason(fx.good_frontier())
    + cif.check_row_evidence_complete(fx.good_frontier())
    + cif.check_metric_expectation(fx.good_frontier())
    + cif.check_cross_check_present(fx.good_frontier())
)

results["bad_MISSING_JOIN"] = cif.check_missing_join(missing_join_path) + cif.check_missing_join(empty_dims_join_path)
committed_json, fresh_json, committed_md, fresh_md = fx.bad_stale_artifact_quad()
results["bad_STALE_ARTIFACT"] = cif.check_stale_artifact(committed_json, fresh_json, committed_md, fresh_md)
results["bad_ROW_ID_UNIQUE"] = cif.check_row_id_unique(fx.bad_row_id_unique_frontier())
results["bad_ROW_ID_PURITY"] = cif.check_row_id_purity(fx.bad_row_id_purity_frontier())
results["bad_EMPTY_QUEUE_REASON"] = cif.check_empty_queue_reason(fx.bad_empty_queue_reason_frontier())
results["bad_ROW_EVIDENCE_COMPLETE"] = cif.check_row_evidence_complete(fx.bad_row_evidence_incomplete_frontier())
results["bad_METRIC_EXPECTATION"] = cif.check_metric_expectation(fx.bad_metric_expectation_frontier())
results["bad_CROSS_CHECK_PRESENT"] = cif.check_cross_check_present(fx.bad_cross_check_missing_frontier())

for name, failures in results.items():
    print(f"{name}={'FAIL' if failures else 'PASS'}")
PYEOF
}

echo "=== baseline (unmutated checker) ==="
clear_pycache
baseline="$(run_all_fixtures)"
echo "$baseline"

good_count="$(echo "$baseline" | grep -c '^good=PASS$')"
if [ "$good_count" -ne 1 ]; then
  echo "FATAL: baseline does not pass the good fixture -- fixtures or checker are broken" >&2
  exit 1
fi
for guard in "${GUARDS[@]}"; do
  count="$(echo "$baseline" | grep -c "^bad_${guard}=FAIL\$")"
  if [ "$count" -ne 1 ]; then
    echo "FATAL: baseline does not reject 'bad_${guard}' -- fixtures or checker are broken" >&2
    exit 1
  fi
done
echo "baseline OK: good passes, all ${#GUARDS[@]} bad fixtures fail"
echo

overall_pass=1
declare -A KILL_TABLE

for guard in "${GUARDS[@]}"; do
  stub="${STUB[$guard]}"
  target="bad_${guard}"

  python3 - "$SCRATCH/scripts/check-infrastructure-frontier.py" "$guard" "$stub" <<'PYEOF'
import re
import sys

path, guard, stub = sys.argv[1], sys.argv[2], sys.argv[3]
stub_text = stub.encode().decode("unicode_escape")
text = open(path, "r", encoding="utf-8").read()
pattern = re.compile(
    r"# GUARD:" + re.escape(guard) + r" begin\n.*?\n# GUARD:" + re.escape(guard) + r" end\n",
    re.DOTALL,
)
replacement = f"# GUARD:{guard} begin\n{stub_text}# GUARD:{guard} end\n"
new_text, n = pattern.subn(replacement, text)
if n != 1:
    print(f"FATAL: expected exactly one GUARD:{guard} block in {path}, found {n}", file=sys.stderr)
    sys.exit(1)
open(path, "w", encoding="utf-8").write(new_text)
PYEOF

  clear_pycache
  echo "=== guard $guard deleted (should flip only '$target') ==="
  mutated_result="$(run_all_fixtures)"
  echo "$mutated_result"

  flipped=()
  for g2 in "${GUARDS[@]}"; do
    f="bad_${g2}"
    line_before="$(echo "$baseline" | grep "^${f}=")"
    line_after="$(echo "$mutated_result" | grep "^${f}=")"
    if [ "$line_before" = "${f}=FAIL" ] && [ "$line_after" = "${f}=PASS" ]; then
      flipped+=("$f")
    fi
  done
  good_after="$(echo "$mutated_result" | grep '^good=')"

  if [ "$good_after" != "good=PASS" ]; then
    echo "FAIL: deleting guard $guard broke the GOOD fixture ($good_after) -- guards must not depend on each other" >&2
    overall_pass=0
  fi

  if [ "${#flipped[@]}" -eq 1 ] && [ "${flipped[0]}" = "$target" ]; then
    echo "PASS: guard $guard kills exactly its target test ($target)"
    KILL_TABLE[$guard]="$target"
  else
    echo "FAIL: guard $guard flipped {${flipped[*]:-none}}, expected exactly {$target}" >&2
    overall_pass=0
  fi
  echo

  cp "$REPO_ROOT/scripts/check-infrastructure-frontier.py" "$SCRATCH/scripts/check-infrastructure-frontier.py"
done

echo "=== guard -> test kill table ==="
for guard in "${GUARDS[@]}"; do
  echo "  $guard -> ${KILL_TABLE[$guard]:-NONE (did not kill exactly its target)}"
done

if [ "$overall_pass" -ne 1 ]; then
  echo "test-infrastructure-frontier-mutations: FAILED" >&2
  exit 1
fi
echo "test-infrastructure-frontier-mutations: all ${#GUARDS[@]} guards kill exactly their own mutation"
