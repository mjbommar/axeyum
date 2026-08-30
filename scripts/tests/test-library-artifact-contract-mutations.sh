#!/usr/bin/env bash
# Guard-deletion kill table for scripts/check-library-artifact-contract.py
# (L1 phase C0, reader A).
#
# CLAUDE.md's standing rule: "when you touch a checker, delete one guard and
# require that EXACTLY ONE test dies." This script builds the six fixture
# packs (the untouched positive pack plus one mutation per C0 mutation
# class), then -- in a SCRATCH COPY of the validator source, never the
# tracked file (CLAUDE.md: "mutation testing in the shared worktree breaks
# other lanes' builds") -- neuters exactly one of the five named guards at a
# time by replacing its function body with `return []`, and re-runs all six
# fixtures through the mutated copy.
#
# The exit criterion: deleting guard G makes ONLY mutation G's fixture start
# passing; the other four mutated fixtures must still fail, and the good
# fixture must still pass (a guard's removal can only make an invalid pack
# look valid, never make a valid one look invalid).
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRATCH="$(mktemp -d "${TMPDIR:-/tmp}/lac-mutation-XXXXXX")"
trap 'rm -rf "$SCRATCH"' EXIT

mkdir -p "$SCRATCH/scripts/tests" "$SCRATCH/fixtures"
cp "$REPO_ROOT/scripts/check-library-artifact-contract.py" "$SCRATCH/scripts/check-library-artifact-contract.py"

/usr/bin/python3 "$REPO_ROOT/scripts/tests/library_artifact_mutations.py" \
  --write-fixtures "$SCRATCH/fixtures" > /dev/null

FIXTURES=(good missing duplicate reordered truncated value_exposed unstated_provenance)
GUARDS=(MISSING DUPLICATE REORDERED TRUNCATED VALUE_EXPOSED PROVENANCE)
# Which fixture each guard is supposed to be the ONLY thing rejecting.
declare -A GUARD_TARGET=(
  [MISSING]=missing
  [DUPLICATE]=duplicate
  [REORDERED]=reordered
  [TRUNCATED]=truncated
  [VALUE_EXPOSED]=value_exposed
  [PROVENANCE]=unstated_provenance
)
declare -A STUB=(
  [MISSING]='def check_missing_roots(pack, population_dir):\n    return []\n'
  [DUPLICATE]='def check_no_duplicate_names(pack):\n    return []\n'
  [REORDERED]='def check_pack_digest(pack):\n    return []\n'
  [TRUNCATED]='def check_record_digests(pack):\n    return []\n'
  [VALUE_EXPOSED]='def check_typeproj_no_value_leak(typeproj_path):\n    return []\n'
  [PROVENANCE]='def check_text_provenance(pack, pack_path):\n    return []\n'
)

clear_pycache() {
  find "$SCRATCH" -name '__pycache__' -exec rm -rf {} + 2>/dev/null || true
}

# Runs the validator against all six fixtures; prints "$fixture=PASS" or
# "$fixture=FAIL" per line.
run_all_fixtures() {
  local validator="$1"
  for f in "${FIXTURES[@]}"; do
    if /usr/bin/python3 "$validator" \
        --pack "$SCRATCH/fixtures/$f.pack.json" \
        --population-dir "$SCRATCH/fixtures/populations" \
        > "$SCRATCH/last-$f.out" 2>&1; then
      echo "$f=PASS"
    else
      echo "$f=FAIL"
    fi
  done
}

echo "=== baseline (unmutated validator) ==="
clear_pycache
baseline="$(run_all_fixtures "$SCRATCH/scripts/check-library-artifact-contract.py")"
echo "$baseline"
good_count="$(echo "$baseline" | grep -c '^good=PASS$')"
if [ "$good_count" -ne 1 ]; then
  echo "FATAL: baseline does not pass the good fixture -- fixtures or validator are broken" >&2
  exit 1
fi
for f in missing duplicate reordered truncated value_exposed unstated_provenance; do
  count="$(echo "$baseline" | grep -c "^${f}=FAIL\$")"
  if [ "$count" -ne 1 ]; then
    echo "FATAL: baseline does not reject '$f' -- fixtures or validator are broken" >&2
    exit 1
  fi
done
echo "baseline OK: good passes, all five mutations fail"
echo

overall_pass=1
declare -A KILL_TABLE

for guard in "${GUARDS[@]}"; do
  target="${GUARD_TARGET[$guard]}"
  stub="${STUB[$guard]}"

  python3 - "$SCRATCH/scripts/check-library-artifact-contract.py" "$guard" "$stub" <<'PYEOF'
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
    print(f"FATAL: expected exactly one GUARD:{guard} block, found {n}", file=sys.stderr)
    sys.exit(1)
open(path, "w", encoding="utf-8").write(new_text)
PYEOF

  clear_pycache
  echo "=== guard $guard deleted (should flip only '$target') ==="
  mutated_result="$(run_all_fixtures "$SCRATCH/scripts/check-library-artifact-contract.py")"
  echo "$mutated_result"

  flipped=()
  for f in "${FIXTURES[@]}"; do
    if [ "$f" = "good" ]; then
      continue
    fi
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
  cp "$REPO_ROOT/scripts/check-library-artifact-contract.py" "$SCRATCH/scripts/check-library-artifact-contract.py"
done

echo "=== guard -> test kill table ==="
for guard in "${GUARDS[@]}"; do
  echo "  $guard -> ${KILL_TABLE[$guard]:-NONE (did not kill exactly its target)}"
done

if [ "$overall_pass" -ne 1 ]; then
  echo "test-library-artifact-contract-mutations: FAILED" >&2
  exit 1
fi
echo "test-library-artifact-contract-mutations: all ${#GUARDS[@]} guards kill exactly their own mutation"
