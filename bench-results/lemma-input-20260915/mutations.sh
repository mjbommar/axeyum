#!/usr/bin/env bash
# LEMMA-INPUT -- R12's second half: each guard of the indexed refresh is deleted
# or corrupted in turn, and the tests are required to DIE.
#
# NEVER IN THE SHARED WORKTREE.  The mutant is on disk for every other lane's
# build and the failures it causes look like their bug, so this operates on a
# `lane-snapshot.sh` copy under /data0 and is pinned to cores the A/B is not on.
#
# The outcome of a mutation is only a MEASUREMENT when the mutant BUILT and the
# suite ran a NONZERO number of tests.  A mutant that fails to compile, or a
# filter that selects nothing, both present as "not clean" and neither supports
# a coverage claim -- so both are printed as themselves.
#
# ONE MUTATION IS EXPECTED TO KILL NOTHING and is included deliberately: the
# unchanged-atom-count early return has no observable effect on OUTPUT by
# construction (it skips work whose result is already held), so no test over
# output can catch it.  That impossibility is the finding, not a gap to paper
# over -- its evidence is the A/B, and this run is what shows the unit tests do
# not silently claim to cover it.
set -u
SNAP="$1"
TARGET="${2:-/data0/axeyum/lemma-input-target-mut}"
SRC="$SNAP/crates/axeyum-solver/src/dpll_lia.rs"
KEEP="$SNAP/dpll_lia.rs.pristine"
cp "$SRC" "$KEEP"

run_suite() {
  local label="$1" out result total
  out=$(cd "$SNAP" && CARGO_BUILD_JOBS=4 CARGO_TARGET_DIR="$TARGET" \
        taskset -c 12-15 cargo test -p axeyum-solver --lib --features full -- \
        the_indexed the_bound_scan_fixture the_cached --test-threads=1 2>&1)
  result=$(printf '%s\n' "$out" | grep -E '^test result' | tail -1)
  total=$(printf '%s\n' "$out" | grep -cE '^test dpll_lia::tests::')
  if [ -z "$result" ]; then
    echo "$label: DID NOT BUILD (no 'test result' line) -- NOT A MEASUREMENT"
    printf '%s\n' "$out" | grep -E '^error' | head -3
    return
  fi
  echo "$label: $result"
  # `^test .* FAILED` also matches the `test result: FAILED.` SUMMARY line, so
  # the count it printed was one too many on the first run. Anchor on the
  # per-test shape instead.
  printf '%s\n' "$out" | grep -E '^test [a-z_:]+ \.\.\. FAILED' | sed 's/^/  DIED: /'
  echo "  tests executed: $total"
  [ "$total" -gt 0 ] || echo "  ZERO TESTS RAN -- NOT A MEASUREMENT"
}

apply() {
  cp "$KEEP" "$SRC"
  python3 - "$SRC" "$1" "$2" <<'PY'
import pathlib, sys
p = pathlib.Path(sys.argv[1])
t = p.read_text()
old, new = sys.argv[2], sys.argv[3]
assert t.count(old) == 1, f"mutation anchor not unique ({t.count(old)}): {old!r}"
p.write_text(t.replace(old, new))
PY
}

echo "== BASELINE (no mutation) =="
run_suite baseline

echo
echo "== M1: the index skips one eligible partner (off by one) =="
apply 'let start = group.partition_point(|&j| j <= i);' \
      'let start = group.partition_point(|&j| j <= i) + 1;'
run_suite M1

echo
echo "== M2: the lookup reads a different group than the insert wrote =="
apply 'let Some(group) = by_expr.get(&bounds[i].expr) else {' \
      'let Some(group) = by_expr.get(&bounds[0].expr) else {'
run_suite M2

echo
echo "== M3: the cached extraction re-reads from zero instead of the suffix =="
apply 'for idx in from..self.ctx.atoms.len() {' 'for idx in 0..self.ctx.atoms.len() {'
run_suite M3

echo
echo "== M4: the unchanged-atom-count early return is deleted =="
echo "   (expected to kill NOTHING -- see the header)"
apply '        if self.initial_bounds_atoms == Some(self.ctx.atoms.len()) {
            return Ok(());
        }' '        if false {
            return Ok(());
        }'
run_suite M4

cp "$KEEP" "$SRC"
echo
echo "restored pristine source"
