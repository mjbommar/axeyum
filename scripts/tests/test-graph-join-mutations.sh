#!/usr/bin/env bash
# Guard-deletion kill table for scripts/check-graph-join.py (L1 phase G2).
# Mirrors scripts/tests/test-declaration-graph-mutations.sh's method, adapted
# to the fact that check-graph-join.py's guards are pure functions over
# already-loaded dicts (fact_ids/kernel_declarations/... resolution), not
# functions over an on-disk pack file -- so fixtures here are the small
# hand-built dicts in scripts/tests/graph_join_mutations.py, driven through a
# tiny Python harness rather than the CLI directly.
#
# CLAUDE.md's standing rule: "when you touch a checker, delete one guard and
# require that EXACTLY ONE test dies." This builds one Python driver per
# guard fixture, then -- in a SCRATCH COPY of check-graph-join.py (never the
# tracked file) -- neuters exactly one guard at a time and re-runs every
# fixture through the mutated copy.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRATCH="$(mktemp -d "${TMPDIR:-/tmp}/gj-mutation-XXXXXX")"
trap 'rm -rf "$SCRATCH"' EXIT

mkdir -p "$SCRATCH/scripts/lib" "$SCRATCH/scripts/tests"
cp "$REPO_ROOT/scripts/check-graph-join.py" "$SCRATCH/scripts/check-graph-join.py"
cp "$REPO_ROOT/scripts/lib/graph_join.py" "$SCRATCH/scripts/lib/graph_join.py"
cp "$REPO_ROOT/scripts/tests/graph_join_mutations.py" "$SCRATCH/scripts/tests/graph_join_mutations.py"
cp "$REPO_ROOT/scripts/check-fact-depends-derived.py" "$SCRATCH/scripts/check-fact-depends-derived.py"

GUARDS=(EMPTY_POPULATION EMPTY_FACTS ACCOUNTING STALE_ARTIFACT POSITIVE_CONTROL BARE_NAME_BASIS)
declare -A STUB=(
  [EMPTY_POPULATION]='def check_empty_population(rows):\n    return []\n'
  [EMPTY_FACTS]='def check_empty_facts(facts_by_id):\n    return []\n'
  [ACCOUNTING]='def check_accounting(join):\n    return []\n'
  [STALE_ARTIFACT]='def check_stale_artifact(committed, fresh):\n    return []\n'
  [POSITIVE_CONTROL]='def check_positive_control(join, facts_by_id):\n    return []\n'
  [BARE_NAME_BASIS]='def check_bare_name_basis(join, facts_by_id, depends_derived):\n    return []\n'
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
import sys

scratch = sys.argv[1]

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod

gj = load("graph_join", f"{scratch}/scripts/lib/graph_join.py")
fx = load("graph_join_mutations", f"{scratch}/scripts/tests/graph_join_mutations.py")
cgj = load("check_graph_join", f"{scratch}/scripts/check-graph-join.py")

results = {}

results["good"] = (
    cgj.check_empty_population(fx.good_rows())
    + cgj.check_empty_facts(fx.good_facts_by_id())
    + cgj.check_accounting(fx.good_join())
    + cgj.check_stale_artifact(fx.good_join(), fx.good_join())
    + cgj.check_positive_control(fx.good_join(), fx.good_facts_by_id())
)
depends_derived = gj._load_depends_derived_module()
results["good"] += cgj.check_bare_name_basis(fx.good_join(), fx.good_facts_by_id(), depends_derived)

results["bad_EMPTY_POPULATION"] = cgj.check_empty_population(fx.bad_empty_population_rows())
results["bad_EMPTY_FACTS"] = cgj.check_empty_facts(fx.bad_empty_facts())
results["bad_ACCOUNTING"] = cgj.check_accounting(fx.bad_accounting_join())
committed, fresh = fx.bad_stale_artifact_pair()
results["bad_STALE_ARTIFACT"] = cgj.check_stale_artifact(committed, fresh)
results["bad_POSITIVE_CONTROL"] = cgj.check_positive_control(
    fx.bad_positive_control_join(), fx.good_facts_by_id()
)
bad_join, bad_facts = fx.bad_bare_name_basis_join_and_facts()
results["bad_BARE_NAME_BASIS"] = cgj.check_bare_name_basis(bad_join, bad_facts, depends_derived)

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
echo "baseline OK: good passes, all six bad fixtures fail"
echo

overall_pass=1
declare -A KILL_TABLE

for guard in "${GUARDS[@]}"; do
  stub="${STUB[$guard]}"
  target="bad_${guard}"

  python3 - "$SCRATCH/scripts/check-graph-join.py" "$guard" "$stub" <<'PYEOF'
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

  cp "$REPO_ROOT/scripts/check-graph-join.py" "$SCRATCH/scripts/check-graph-join.py"
done

echo "=== guard -> test kill table ==="
for guard in "${GUARDS[@]}"; do
  echo "  $guard -> ${KILL_TABLE[$guard]:-NONE (did not kill exactly its target)}"
done

if [ "$overall_pass" -ne 1 ]; then
  echo "test-graph-join-mutations: FAILED" >&2
  exit 1
fi
echo "test-graph-join-mutations: all ${#GUARDS[@]} guards kill exactly their own mutation"
