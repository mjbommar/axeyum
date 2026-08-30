#!/usr/bin/env bash
# Guard-deletion kill table for scripts/check-declaration-graph.py (L1 phase
# C1/G1). Mirrors scripts/tests/test-library-artifact-contract-mutations.sh's
# method exactly (ADR-0800), extended to the three new guards this file adds
# on top of ADR-0800's five reused ones.
#
# CLAUDE.md's standing rule: "when you touch a checker, delete one guard and
# require that EXACTLY ONE test dies." This builds nine fixtures (the good
# graph plus one mutation per class), then -- in a SCRATCH COPY of BOTH
# check-declaration-graph.py and check-library-artifact-contract.py (never
# the tracked files: "mutation testing in the shared worktree breaks other
# lanes' builds") -- neuters exactly one guard at a time and re-runs all nine
# fixtures through the mutated copy.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRATCH="$(mktemp -d "${TMPDIR:-/tmp}/dg-mutation-XXXXXX")"
trap 'rm -rf "$SCRATCH"' EXIT

mkdir -p "$SCRATCH/scripts/lib" "$SCRATCH/scripts/tests" "$SCRATCH/fixtures"
cp "$REPO_ROOT/scripts/check-declaration-graph.py" "$SCRATCH/scripts/check-declaration-graph.py"
cp "$REPO_ROOT/scripts/check-library-artifact-contract.py" "$SCRATCH/scripts/check-library-artifact-contract.py"
cp "$REPO_ROOT/scripts/lib/declaration_graph.py" "$SCRATCH/scripts/lib/declaration_graph.py"

# Both declaration_graph.py's `REPO_ROOT` and check-declaration-graph.py's own
# `REPO_ROOT` are computed from `__file__`, not hardcoded -- so copying the
# three files into the SAME relative layout under $SCRATCH is sufficient for
# declaration_graph.py's `_lac()` to load the SCRATCH copy of
# check-library-artifact-contract.py (where MISSING/DUPLICATE/REORDERED/
# TRUNCATED/VALUE_EXPOSED get mutated below), not the tracked one. No path
# patching needed; verified by the baseline check immediately below actually
# exercising all eight guards against the scratch tree.

/usr/bin/python3 "$REPO_ROOT/scripts/tests/declaration_graph_mutations.py" \
  --write-fixtures "$SCRATCH/fixtures" > /dev/null

FIXTURES=(good missing duplicate reordered truncated value_exposed row_deleted edge_deleted unexpected_cycle)
GUARDS=(MISSING DUPLICATE REORDERED TRUNCATED VALUE_EXPOSED ENDPOINT_RESOLUTION EDGES_CONSISTENT CYCLE_CLASSIFICATION)
declare -A GUARD_TARGET=(
  [MISSING]=missing
  [DUPLICATE]=duplicate
  [REORDERED]=reordered
  [TRUNCATED]=truncated
  [VALUE_EXPOSED]=value_exposed
  [ENDPOINT_RESOLUTION]=row_deleted
  [EDGES_CONSISTENT]=edge_deleted
  [CYCLE_CLASSIFICATION]=unexpected_cycle
)
# Which file the guard's `# GUARD:<NAME> begin/end` block lives in, and the
# stub to replace it with.
declare -A GUARD_FILE=(
  [MISSING]="$SCRATCH/scripts/check-library-artifact-contract.py"
  [DUPLICATE]="$SCRATCH/scripts/check-library-artifact-contract.py"
  [REORDERED]="$SCRATCH/scripts/check-library-artifact-contract.py"
  [TRUNCATED]="$SCRATCH/scripts/check-library-artifact-contract.py"
  [VALUE_EXPOSED]="$SCRATCH/scripts/check-library-artifact-contract.py"
  [ENDPOINT_RESOLUTION]="$SCRATCH/scripts/check-declaration-graph.py"
  [EDGES_CONSISTENT]="$SCRATCH/scripts/check-declaration-graph.py"
  [CYCLE_CLASSIFICATION]="$SCRATCH/scripts/check-declaration-graph.py"
)
declare -A STUB=(
  [MISSING]='def check_missing_roots(pack, population_dir):\n    return []\n'
  [DUPLICATE]='def check_no_duplicate_names(pack):\n    return []\n'
  [REORDERED]='def check_pack_digest(pack):\n    return []\n'
  [TRUNCATED]='def check_record_digests(pack):\n    return []\n'
  [VALUE_EXPOSED]='def check_typeproj_no_value_leak(typeproj_path):\n    return []\n'
  [ENDPOINT_RESOLUTION]='def check_endpoint_resolution(pack):\n    return []\n'
  [EDGES_CONSISTENT]='def check_edges_consistent(pack, edges_path):\n    return []\n'
  [CYCLE_CLASSIFICATION]='def check_cycle_classification(pack, cycles_path):\n    return []\n'
)

clear_pycache() {
  find "$SCRATCH" -name '__pycache__' -exec rm -rf {} + 2>/dev/null || true
}

run_all_fixtures() {
  for f in "${FIXTURES[@]}"; do
    if /usr/bin/python3 "$SCRATCH/scripts/check-declaration-graph.py" \
        --rows "$SCRATCH/fixtures/$f.rows.json" \
        --population-dir "$SCRATCH/fixtures/populations" \
        > "$SCRATCH/last-$f.out" 2>&1; then
      echo "$f=PASS"
    else
      echo "$f=FAIL"
    fi
  done
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
for f in "${FIXTURES[@]}"; do
  [ "$f" = "good" ] && continue
  count="$(echo "$baseline" | grep -c "^${f}=FAIL\$")"
  if [ "$count" -ne 1 ]; then
    echo "FATAL: baseline does not reject '$f' -- fixtures or checker are broken" >&2
    exit 1
  fi
done
echo "baseline OK: good passes, all eight mutations fail"
echo

overall_pass=1
declare -A KILL_TABLE

for guard in "${GUARDS[@]}"; do
  target="${GUARD_TARGET[$guard]}"
  stub="${STUB[$guard]}"
  file="${GUARD_FILE[$guard]}"

  python3 - "$file" "$guard" "$stub" <<'PYEOF'
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
  for f in "${FIXTURES[@]}"; do
    [ "$f" = "good" ] && continue
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

  # Restore the pristine copy for the next guard's turn.
  cp "$REPO_ROOT/scripts/check-declaration-graph.py" "$SCRATCH/scripts/check-declaration-graph.py"
  cp "$REPO_ROOT/scripts/check-library-artifact-contract.py" "$SCRATCH/scripts/check-library-artifact-contract.py"
done

echo "=== guard -> test kill table ==="
for guard in "${GUARDS[@]}"; do
  echo "  $guard -> ${KILL_TABLE[$guard]:-NONE (did not kill exactly its target)}"
done

if [ "$overall_pass" -ne 1 ]; then
  echo "test-declaration-graph-mutations: FAILED" >&2
  exit 1
fi
echo "test-declaration-graph-mutations: all ${#GUARDS[@]} guards kill exactly their own mutation"
