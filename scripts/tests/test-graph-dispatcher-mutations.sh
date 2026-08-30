#!/usr/bin/env bash
# Guard-deletion kill table for scripts/check-graph-dispatcher.py (L2 phase
# G5). Mirrors scripts/tests/test-infrastructure-frontier-mutations.sh's
# method: check-graph-dispatcher.py's guards are pure functions over
# already-loaded dicts/strings/paths, so fixtures are the small hand-built
# values in scripts/tests/graph_dispatcher_mutations.py, driven through a
# tiny Python harness -- in a SCRATCH COPY of check-graph-dispatcher.py
# (never the tracked file) -- neutering exactly one guard at a time and
# re-running every fixture through the mutated copy.
#
# CLAUDE.md's standing rule: "when you touch a checker, delete one guard and
# require that EXACTLY ONE test dies." Every guard below is IN the kill
# table produced at the end, not merely exercised beside it.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRATCH="$(mktemp -d "${TMPDIR:-/tmp}/gd-mutation-XXXXXX")"
trap 'rm -rf "$SCRATCH"' EXIT

mkdir -p "$SCRATCH/scripts/lib" "$SCRATCH/scripts/tests" "$SCRATCH/fixtures"
cp "$REPO_ROOT/scripts/check-graph-dispatcher.py" "$SCRATCH/scripts/check-graph-dispatcher.py"
cp "$REPO_ROOT/scripts/lib/graph_dispatcher.py" "$SCRATCH/scripts/lib/graph_dispatcher.py"
cp "$REPO_ROOT/scripts/tests/graph_dispatcher_mutations.py" "$SCRATCH/scripts/tests/graph_dispatcher_mutations.py"

GUARDS=(MISSING_INPUTS NO_DESTINATION NO_CAPABILITY UPSTREAM_GUARD_PROPAGATION LEGAL_TARGET_PRESENT HELD_OUT_NEVER_PROPOSED AUTHORITY_SCOPE ROW_CITATION_VALID OVERRIDE_LEDGER_COMPLETE ADR_CITATION_PRESENT)
declare -A STUB=(
  [MISSING_INPUTS]='def check_missing_inputs(curriculum_path, frontier_dir):\n    return []\n'
  [NO_DESTINATION]='def check_no_destination(destination, error):\n    return []\n'
  [NO_CAPABILITY]='def check_no_capability(capability, error):\n    return []\n'
  [UPSTREAM_GUARD_PROPAGATION]='def check_upstream_guard_propagation(dispatch_result, dispatch_error):\n    return []\n'
  [LEGAL_TARGET_PRESENT]='def check_legal_target_present(dispatchable_count, legal_target_fact_id):\n    return []\n'
  [HELD_OUT_NEVER_PROPOSED]='def check_held_out_never_proposed(legal_target_fact_id, override_targets, forbidden):\n    return []\n'
  [AUTHORITY_SCOPE]='def check_authority_scope(recommendation):\n    return []\n'
  [ROW_CITATION_VALID]='def check_row_citation_valid(recommendation, frontier_docs):\n    return []\n'
  [OVERRIDE_LEDGER_COMPLETE]='def check_override_ledger_complete(entries):\n    return []\n'
  [ADR_CITATION_PRESENT]='def check_adr_citation_present(citations):\n    return []\n'
)

clear_pycache() {
  find "$SCRATCH" -name '__pycache__' -exec rm -rf {} + 2>/dev/null || true
}

run_all_fixtures() {
  PYTHONPATH="$SCRATCH/scripts:$SCRATCH/scripts/lib:$SCRATCH/scripts/tests" REPO_ROOT_FOR_ADR="$REPO_ROOT" /usr/bin/python3 - "$SCRATCH" <<'PYEOF'
import importlib.util
import os
import sys
from pathlib import Path

scratch = Path(sys.argv[1])
repo_root = Path(os.environ["REPO_ROOT_FOR_ADR"])

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod

fx = load("graph_dispatcher_mutations", scratch / "scripts/tests/graph_dispatcher_mutations.py")
cgd = load("check_graph_dispatcher", scratch / "scripts/check-graph-dispatcher.py")

results = {}

# MISSING_INPUTS -- needs real files, and ADR_CITATION_PRESENT needs the REAL
# repo root so the good fixture's cited ADR paths actually resolve (the
# scratch tree does not carry docs/).
cgd.REPO_ROOT = repo_root

good_curr, good_front = fx.missing_inputs_good(scratch / "fixtures" / "mi_good")
bad_curr_curr, bad_curr_front = fx.missing_inputs_bad_curriculum(scratch / "fixtures" / "mi_bad_curr")
bad_front_curr, bad_front_front = fx.missing_inputs_bad_frontier(scratch / "fixtures" / "mi_bad_front")

def all_good_guards():
    dest, dest_err = fx.no_destination_good()
    cap, cap_err = fx.no_capability_good()
    return (
        cgd.check_missing_inputs(good_curr, good_front)
        + cgd.check_no_destination(dest, dest_err)
        + cgd.check_no_capability(cap, cap_err)
        + cgd.check_upstream_guard_propagation(*[fx.upstream_good_clean(), None])
        + cgd.check_legal_target_present(*fx.legal_target_present_good())
        + cgd.check_held_out_never_proposed(*fx.held_out_good())
        + cgd.check_authority_scope(fx.authority_scope_good())
        + cgd.check_row_citation_valid(*fx.row_citation_good())
        + cgd.check_override_ledger_complete(fx.override_ledger_good())
        + cgd.check_adr_citation_present(fx.adr_citation_good())
    )

results["good"] = all_good_guards()

results["bad_MISSING_INPUTS"] = (
    cgd.check_missing_inputs(bad_curr_curr, bad_curr_front)
    + cgd.check_missing_inputs(bad_front_curr, bad_front_front)
)
results["bad_NO_DESTINATION"] = cgd.check_no_destination(*fx.no_destination_bad())
results["bad_NO_CAPABILITY"] = cgd.check_no_capability(*fx.no_capability_bad())
results["bad_UPSTREAM_GUARD_PROPAGATION"] = cgd.check_upstream_guard_propagation(fx.upstream_bad(), None)
results["bad_LEGAL_TARGET_PRESENT"] = cgd.check_legal_target_present(*fx.legal_target_present_bad())
results["bad_HELD_OUT_NEVER_PROPOSED"] = (
    cgd.check_held_out_never_proposed(*fx.held_out_bad_default())
    + cgd.check_held_out_never_proposed(*fx.held_out_bad_override())
)
results["bad_AUTHORITY_SCOPE"] = (
    cgd.check_authority_scope(fx.authority_scope_bad_capability_out_of_scope())
    + cgd.check_authority_scope(fx.authority_scope_bad_fallback_authoritative())
)
results["bad_ROW_CITATION_VALID"] = cgd.check_row_citation_valid(*fx.row_citation_bad())
results["bad_OVERRIDE_LEDGER_COMPLETE"] = (
    cgd.check_override_ledger_complete(fx.override_ledger_bad_short_note())
    + cgd.check_override_ledger_complete(fx.override_ledger_bad_unnamed())
    + cgd.check_override_ledger_complete(fx.override_ledger_bad_no_lane())
)
results["bad_ADR_CITATION_PRESENT"] = (
    cgd.check_adr_citation_present(fx.adr_citation_bad_missing_0865())
    + cgd.check_adr_citation_present(fx.adr_citation_bad_nonexistent_path())
)

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

  python3 - "$SCRATCH/scripts/check-graph-dispatcher.py" "$guard" "$stub" <<'PYEOF'
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

  # Restore the pristine copy for the next guard's mutation.
  cp "$REPO_ROOT/scripts/check-graph-dispatcher.py" "$SCRATCH/scripts/check-graph-dispatcher.py"
done

echo "=== kill table ==="
for guard in "${GUARDS[@]}"; do
  printf '  %-28s -> %s\n' "$guard" "${KILL_TABLE[$guard]:-NONE}"
done

if [ "${#KILL_TABLE[@]}" -ne "${#GUARDS[@]}" ]; then
  echo "FAIL: kill table has ${#KILL_TABLE[@]} entries, expected ${#GUARDS[@]} (every guard must be IN the table)" >&2
  overall_pass=0
fi

if [ "$overall_pass" -eq 1 ]; then
  echo "OK: all ${#GUARDS[@]} guards each kill exactly their own fixture"
  exit 0
else
  echo "FAIL: mutation testing found a guard that is not doing its own job" >&2
  exit 1
fi
