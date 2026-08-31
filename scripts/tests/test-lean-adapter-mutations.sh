#!/usr/bin/env bash
# Guard-deletion kill table for scripts/check-lean-adapter.py (L4 phase C3).
# Mirrors scripts/tests/test-checked-interchange-mutations.sh's method: a
# SCRATCH COPY of the checker (never the tracked file) has exactly one guard
# neutered at a time, and every fixture in lean_adapter_mutations.py is
# re-run through it. CLAUDE.md's standing rule: delete one guard, require
# EXACTLY ONE fixture to flip from FAIL to PASS.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRATCH="$(mktemp -d "${TMPDIR:-/tmp}/ci-mutation-XXXXXX")"
trap 'rm -rf "$SCRATCH"' EXIT

mkdir -p "$SCRATCH/scripts/tests"
cp "$REPO_ROOT/scripts/check-lean-adapter.py" "$SCRATCH/scripts/check-lean-adapter.py"
cp "$REPO_ROOT/scripts/tests/lean_adapter_mutations.py" "$SCRATCH/scripts/tests/lean_adapter_mutations.py"

GUARDS=(ABSENCE LEAN_ACTUALLY_RAN SUCCESS_ACCEPTED MUTATIONS_REJECTED DECLINES_TYPED_NONVACUOUS EXPECTED_MATCHES_OBSERVED ENVIRONMENT_TOOLCHAIN_STALE)
declare -A STUB=(
  [ABSENCE]='def check_absence(goal_pack, result):\n    return []\n'
  [LEAN_ACTUALLY_RAN]='def check_lean_actually_ran(result):\n    return []\n'
  [SUCCESS_ACCEPTED]='def check_success_accepted(result):\n    return []\n'
  [MUTATIONS_REJECTED]='def check_mutations_rejected(result):\n    return []\n'
  [DECLINES_TYPED_NONVACUOUS]='def check_declines_typed_nonvacuous(result):\n    return []\n'
  [EXPECTED_MATCHES_OBSERVED]='def check_expected_matches_observed(result):\n    return []\n'
  [ENVIRONMENT_TOOLCHAIN_STALE]='def check_environment_toolchain_stale(result, live_identity):\n    return []\n'
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


fx = load("lean_adapter_mutations", f"{scratch}/scripts/tests/lean_adapter_mutations.py")
cla = load("check_lean_adapter", f"{scratch}/scripts/check-lean-adapter.py")

results = {}

good_pack = fx.good_goal_pack()
good_res = fx.good_result()
good_id = fx.good_live_identity()

results["good"] = (
    cla.check_absence(good_pack, good_res)
    + cla.check_lean_actually_ran(good_res)
    + cla.check_success_accepted(good_res)
    + cla.check_mutations_rejected(good_res)
    + cla.check_declines_typed_nonvacuous(good_res)
    + cla.check_expected_matches_observed(good_res)
    + cla.check_environment_toolchain_stale(good_res, good_id)
)

results["bad_ABSENCE"] = cla.check_absence(good_pack, fx.bad_absence_result())
results["bad_LEAN_ACTUALLY_RAN"] = cla.check_lean_actually_ran(fx.bad_lean_actually_ran_result())
results["bad_SUCCESS_ACCEPTED"] = cla.check_success_accepted(fx.bad_success_accepted_result())
results["bad_MUTATIONS_REJECTED"] = cla.check_mutations_rejected(fx.bad_mutations_rejected_result())
results["bad_DECLINES_TYPED_NONVACUOUS"] = cla.check_declines_typed_nonvacuous(
    fx.bad_declines_typed_nonvacuous_result()
)
results["bad_EXPECTED_MATCHES_OBSERVED"] = cla.check_expected_matches_observed(
    fx.bad_expected_matches_observed_result()
)
results["bad_ENVIRONMENT_TOOLCHAIN_STALE"] = cla.check_environment_toolchain_stale(
    fx.bad_environment_toolchain_stale_result(), good_id
)

for name, failures in results.items():
    print(f"{name}={'FAIL' if failures else 'PASS'}")
PYEOF
}

echo "== baseline (no guard removed) =="
clear_pycache
baseline="$(run_all_fixtures)"
echo "$baseline"

echo "$baseline" | grep -qx 'good=PASS' || {
  echo "FAIL: the good fixture must pass every guard in the baseline" >&2
  exit 1
}
for guard in "${GUARDS[@]}"; do
  echo "$baseline" | grep -qx "bad_${guard}=FAIL" || {
    echo "FAIL: fixture bad_${guard} must FAIL in the baseline (guard intact)" >&2
    exit 1
  }
done

overall_ok=1
for guard in "${GUARDS[@]}"; do
  echo "== neutering guard: $guard =="
  cp "$REPO_ROOT/scripts/check-lean-adapter.py" "$SCRATCH/scripts/check-lean-adapter.py"
  python3 - "$SCRATCH/scripts/check-lean-adapter.py" "$guard" "${STUB[$guard]}" <<'PYEOF'
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
