#!/usr/bin/env bash
# Guard-deletion kill table for scripts/check-checked-interchange.py (L4
# phase C2). Mirrors scripts/tests/test-graph-join-mutations.sh's method: a
# SCRATCH COPY of the checker (never the tracked file) has exactly one guard
# neutered at a time, and every fixture in checked_interchange_mutations.py is
# re-run through it. CLAUDE.md's standing rule: delete one guard, require
# EXACTLY ONE fixture to flip from FAIL to PASS.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRATCH="$(mktemp -d "${TMPDIR:-/tmp}/ci-mutation-XXXXXX")"
trap 'rm -rf "$SCRATCH"' EXIT

mkdir -p "$SCRATCH/scripts/tests"
cp "$REPO_ROOT/scripts/check-checked-interchange.py" "$SCRATCH/scripts/check-checked-interchange.py"
cp "$REPO_ROOT/scripts/tests/checked_interchange_mutations.py" "$SCRATCH/scripts/tests/checked_interchange_mutations.py"

GUARDS=(MISSING STALE_POPULATION ACCOUNTING MANDATORY_MISSING_ZERO BARE_NAME_ACCEPT BARE_TYPE_ACCEPT DECLINE_PROBE_VACUOUS)
declare -A STUB=(
  [MISSING]='def check_missing(population, census):\n    return []\n'
  [STALE_POPULATION]='def check_stale_population(population, live_credited_roots):\n    return []\n'
  [ACCOUNTING]='def check_accounting(census):\n    return []\n'
  [MANDATORY_MISSING_ZERO]='def check_mandatory_missing_zero(census):\n    return []\n'
  [BARE_NAME_ACCEPT]='def check_bare_name_accept(census):\n    return []\n'
  [BARE_TYPE_ACCEPT]='def check_bare_type_accept(census):\n    return []\n'
  [DECLINE_PROBE_VACUOUS]='def check_decline_probe_vacuous(census):\n    return []\n'
)

clear_pycache() {
  find "$SCRATCH" -name '__pycache__' -exec rm -rf {} + 2>/dev/null || true
}

run_all_fixtures() {
  PYTHONPATH="$SCRATCH/scripts:$SCRATCH/scripts/tests" /usr/bin/python3 - "$SCRATCH" <<'PYEOF'
import importlib.util
import sys

scratch = sys.argv[1]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


fx = load("checked_interchange_mutations", f"{scratch}/scripts/tests/checked_interchange_mutations.py")
cci = load("check_checked_interchange", f"{scratch}/scripts/check-checked-interchange.py")

results = {}

results["good"] = (
    cci.check_missing(fx.good_population(), fx.good_census())
    + cci.check_stale_population(fx.good_population(), fx.good_live_credited_roots())
    + cci.check_accounting(fx.good_census())
    + cci.check_mandatory_missing_zero(fx.good_census())
    + cci.check_bare_name_accept(fx.good_census())
    + cci.check_bare_type_accept(fx.good_census())
    + cci.check_decline_probe_vacuous(fx.good_census())
)

results["bad_MISSING"] = cci.check_missing(fx.good_population(), fx.bad_missing_census())
results["bad_STALE_POPULATION"] = cci.check_stale_population(
    fx.good_population(), fx.bad_stale_live_credited_roots()
)
results["bad_ACCOUNTING"] = cci.check_accounting(fx.bad_accounting_census())
results["bad_MANDATORY_MISSING_ZERO"] = cci.check_mandatory_missing_zero(
    fx.bad_mandatory_missing_nonzero_census()
)
results["bad_BARE_NAME_ACCEPT"] = cci.check_bare_name_accept(fx.bad_bare_name_accept_census())
results["bad_BARE_TYPE_ACCEPT"] = cci.check_bare_type_accept(fx.bad_bare_type_accept_census())
results["bad_DECLINE_PROBE_VACUOUS"] = cci.check_decline_probe_vacuous(
    fx.bad_decline_probe_vacuous_census()
)

for name, failures in results.items():
    print(f"{name}={'FAIL' if failures else 'PASS'}")
PYEOF
}

echo "== baseline (no guard removed) =="
clear_pycache
baseline="$(run_all_fixtures)"
echo "$baseline"

[ "$(echo "$baseline" | grep -cx 'good=PASS')" -gt 0 ] || {
  echo "FAIL: the good fixture must pass every guard in the baseline" >&2
  exit 1
}
for guard in "${GUARDS[@]}"; do
  [ "$(echo "$baseline" | grep -cx "bad_${guard}=FAIL")" -gt 0 ] || {
    echo "FAIL: fixture bad_${guard} must FAIL in the baseline (guard intact)" >&2
    exit 1
  }
done

overall_ok=1
for guard in "${GUARDS[@]}"; do
  echo "== neutering guard: $guard =="
  cp "$REPO_ROOT/scripts/check-checked-interchange.py" "$SCRATCH/scripts/check-checked-interchange.py"
  python3 - "$SCRATCH/scripts/check-checked-interchange.py" "$guard" "${STUB[$guard]}" <<'PYEOF'
import re
import sys

path, guard, stub = sys.argv[1], sys.argv[2], sys.argv[3]
stub = stub.replace("\\n", "\n")
text = open(path, "r", encoding="utf-8").read()
begin = f"# GUARD:{guard} begin"
end = f"# GUARD:{guard} end"
start = text.index(begin) + len(begin)
finish = text.index(end)
text = text[:start] + "\n" + stub + text[finish:]
open(path, "w", encoding="utf-8").write(text)
PYEOF
  clear_pycache
  mutated="$(run_all_fixtures)"
  echo "$mutated"

  flipped=()
  while IFS= read -r line; do
    name="${line%%=*}"
    value="${line##*=}"
    [ "$name" = "good" ] && continue
    baseline_value="$(echo "$baseline" | grep -x "${name}=.*" | cut -d= -f2)"
    if [ "$value" != "$baseline_value" ]; then
      flipped+=("$name")
    fi
  done <<< "$mutated"

  if [ "${#flipped[@]}" -ne 1 ] || [ "${flipped[0]}" != "bad_${guard}" ]; then
    echo "FAIL: neutering $guard flipped {${flipped[*]:-none}}, expected exactly {bad_${guard}}" >&2
    overall_ok=0
  else
    echo "OK: neutering $guard flips exactly bad_${guard}"
  fi
done

if [ "$overall_ok" -ne 1 ]; then
  echo "MUTATION KILL TABLE FAILED" >&2
  exit 1
fi
echo "MUTATION KILL TABLE PASSED -- ${#GUARDS[@]} guards, each kills exactly its own fixture"
