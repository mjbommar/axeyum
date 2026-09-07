#!/usr/bin/env bash
#
# Control suite for `scripts/measure-producer-channel.py`.
#
# WHY THIS EXISTS. A checker that cannot fail is worse than no checker: it does
# not slow the flywheel, it makes it manufacture unfalsifiable claims at full
# speed. So every guard in the producer-channel metric has ONE control here, and
# each control asserts on that guard's OWN finding text, not merely on a nonzero
# exit. Asserting on exit status alone would let several guards share one test,
# which is exactly the failure the six-of-seven-removable-guards audit found.
#
# THE RULE THIS ENFORCES. `--guard-deletion` deletes each `# GUARD:<id>` line
# group in turn and requires that EXACTLY ONE control dies. A guard whose
# deletion kills zero controls is untested; one whose deletion kills two is
# sharing a rejection path with another guard and neither is independently
# verified.
#
# ISOLATION. Every mutant is written to a scratch root, never to the worktree:
# a mutant on disk is in every other lane's build and its failures look like
# their bug.
#
# Usage:
#   scripts/tests/test-producer-channel-controls.sh              # run controls
#   scripts/tests/test-producer-channel-controls.sh --guard-deletion
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRIPT="$ROOT/scripts/measure-producer-channel.py"
BASELINE="$ROOT/scripts/producer-channel-baseline.json"
KERNEL_SRC="$ROOT/crates/axeyum-lean-kernel/src"
FACTS="$ROOT/artifacts/facts"

SCRATCH="$(mktemp -d "${TMPDIR:-/tmp}/producer-channel-controls.XXXXXX")"
trap 'rm -rf "$SCRATCH"' EXIT

PASS=0
FAIL=0
DIED=()

# run_variant <script> <baseline> <facts> -> writes $SCRATCH/out, echoes exit
run_variant() {
  local script="$1" baseline="$2" facts="$3"
  AXEYUM_PRODUCER_CHANNEL_KERNEL_SRC="$KERNEL_SRC" \
  AXEYUM_PRODUCER_CHANNEL_FACTS="$facts" \
  AXEYUM_PRODUCER_CHANNEL_BASELINE="$baseline" \
    python3 "$script" --check >"$SCRATCH/out" 2>&1
  echo $?
}

# expect_finding <name> <script> <baseline> <facts> <needle>
#   The mutant must exit NONZERO *and* print this guard's own finding text.
expect_finding() {
  local name="$1" script="$2" baseline="$3" facts="$4" needle="$5"
  local rc
  rc="$(run_variant "$script" "$baseline" "$facts")"
  if [ "$rc" -ne 0 ] && grep -F -- "$needle" "$SCRATCH/out" >/dev/null; then
    [ "${QUIET:-0}" = 1 ] || echo "  PASS  $name"
    PASS=$((PASS + 1))
  else
    [ "${QUIET:-0}" = 1 ] || echo "  FAIL  $name  (exit=$rc, needle not found: $needle)"
    FAIL=$((FAIL + 1))
    DIED+=("$name")
  fi
}

# ---------------------------------------------------------------------------
# Mutant construction. Each writes one variant into $SCRATCH.
# ---------------------------------------------------------------------------
build_mutants() {
  local src="${1:-$SCRIPT}"

  # M1 -> GUARD:unclassified.  Disabling `strip_noise` makes the census read
  # producer paths out of `.expect("linarith::generic …")` panic strings and
  # `//!` docs. `generic` is a module, not an entry point, so it lands in no
  # bucket. Measured when this was a real defect: 2 false positives in
  # creal/linarith_bridge.rs.
  sed 's/^        text = strip_noise(path.read_text())$/        text = path.read_text()/' \
    "$src" >"$SCRATCH/m1.py"

  # M2 -> GUARD:vacuous-emit.  An empty EMIT set: nothing is producer-emitted,
  # so the report has nothing to say and would otherwise say it cheerfully.
  python3 - "$src" "$SCRATCH/m2.py" <<'PY'
import sys, re
src, dst = sys.argv[1], sys.argv[2]
t = open(src).read()
t = re.sub(r'^EMIT = \{[^}]*\}', 'EMIT = set()', t, count=1, flags=re.M | re.S)
open(dst, "w").write(t)
PY

  # M4 -> GUARD:blind-join.  Ledger rows stop carrying formal.kernel_theorem,
  # so L3 has no join key at all and its numerator is 0 for a reason that is
  # not "no producer emitted anything".
  sed 's/^        name = data.get("formal", {}).get("kernel_theorem")$/        name = None/' \
    "$src" >"$SCRATCH/m4.py"
}

build_inputs() {
  # M3 -> GUARD:vacuous-ledger.  An empty fact directory.
  mkdir -p "$SCRATCH/empty-facts"

  # M5 -> GUARD:floor-missing.  A baseline that has dropped a floor key.
  python3 - "$BASELINE" "$SCRATCH/baseline-missing.json" <<'PY'
import sys, json
d = json.load(open(sys.argv[1]))
d.pop("producer_emitted_proved_facts", None)
json.dump(d, open(sys.argv[2], "w"), indent=2)
PY

  # M6 -> GUARD:floor-breach.  A floor one above today's measurement, which is
  # what a real shrink of the producer channel looks like from the gate's side.
  python3 - "$BASELINE" "$SCRATCH/baseline-raised.json" <<'PY'
import sys, json
d = json.load(open(sys.argv[1]))
d["emit_sites"] = d["emit_sites"] + 1
json.dump(d, open(sys.argv[2], "w"), indent=2)
PY
}

run_controls() {
  local src="${1:-$SCRIPT}"
  PASS=0; FAIL=0; DIED=()
  build_mutants "$src"
  expect_finding "unclassified   (strip_noise disabled)" \
    "$SCRATCH/m1.py" "$BASELINE" "$FACTS" "in no bucket"
  expect_finding "vacuous-emit   (EMIT set emptied)" \
    "$SCRATCH/m2.py" "$BASELINE" "$FACTS" "zero EMIT sites"
  expect_finding "vacuous-ledger (empty fact directory)" \
    "$src" "$BASELINE" "$SCRATCH/empty-facts" "zero proved facts"
  expect_finding "blind-join     (kernel_theorem dropped)" \
    "$SCRATCH/m4.py" "$BASELINE" "$FACTS" "L3 is blind"
  expect_finding "floor-missing  (baseline key removed)" \
    "$src" "$SCRATCH/baseline-missing.json" "$FACTS" "has no floor"
  expect_finding "floor-breach   (floor raised by one)" \
    "$src" "$SCRATCH/baseline-raised.json" "$FACTS" "fell from"
}

# ---------------------------------------------------------------------------
# Guard deletion: delete one guard, require EXACTLY ONE control to die.
# ---------------------------------------------------------------------------
guard_deletion() {
  local ids rc_all=0
  ids="$(grep -o '# GUARD:[a-z-]*' "$SCRIPT" | sed 's/# GUARD://' | sort -u)"
  if [ -z "$ids" ]; then
    echo "FAIL: no # GUARD: markers found — guard deletion cannot run" >&2
    return 1
  fi
  echo "Guard-deletion table (delete one guard, expect EXACTLY ONE control to die)"
  echo
  printf '  %-16s %-10s %-10s %s\n' guard predicted ran verdict
  printf '  %-16s %-10s %-10s %s\n' ---------------- ---------- ---------- -------
  for id in $ids; do
    grep -v "# GUARD:$id\$" "$SCRIPT" >"$SCRATCH/nog.py"
    python3 -c "import ast,sys; ast.parse(open(sys.argv[1]).read())" "$SCRATCH/nog.py" 2>/dev/null
    if [ $? -ne 0 ]; then
      printf '  %-16s %-10s %-10s %s\n' "$id" 1 "n/a" "SKIPPED (deletion does not parse)"
      rc_all=1
      continue
    fi
    QUIET=1 run_controls "$SCRATCH/nog.py"
    local verdict="ok"
    if [ "$FAIL" -ne 1 ]; then verdict="WRONG"; rc_all=1; fi
    printf '  %-16s %-10s %-10s %s' "$id" 1 "$FAIL" "$verdict"
    if [ "${#DIED[@]}" -gt 0 ]; then printf '  died: %s' "${DIED[*]}"; fi
    printf '\n'
  done
  echo
  return $rc_all
}

# ---------------------------------------------------------------------------
build_inputs

echo "Unmutated script, no environment overrides (a gate must not need a shell):"
env -u AXEYUM_PRODUCER_CHANNEL_KERNEL_SRC \
    -u AXEYUM_PRODUCER_CHANNEL_FACTS \
    -u AXEYUM_PRODUCER_CHANNEL_BASELINE \
    python3 "$SCRIPT" --check >"$SCRATCH/clean" 2>&1
CLEAN=$?
if [ "$CLEAN" -eq 0 ] && grep -F "No findings." "$SCRATCH/clean" >/dev/null; then
  echo "  PASS  clean run is green"
else
  echo "  FAIL  clean run: exit=$CLEAN"
  tail -20 "$SCRATCH/clean"
  exit 1
fi
echo

if [ "${1:-}" = "--guard-deletion" ]; then
  guard_deletion
  exit $?
fi

echo "Controls (each mutant must produce its OWN guard's finding):"
run_controls
echo
echo "controls: $PASS passed, $FAIL failed"
[ "$FAIL" -eq 0 ] || exit 1
