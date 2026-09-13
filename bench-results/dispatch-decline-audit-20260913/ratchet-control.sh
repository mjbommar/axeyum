#!/usr/bin/env bash
# Negative control for the `--fail-on-new` ratchet: re-introduce ONE of the
# propagation sites this lane closed and require the ratchet to exit non-zero.
# A ratchet that has never been shown to fire is not a gate.
set -u
S=/data0/axeyum/scratch/snap-dispatch-decline-audit-b47972ab9
W=/home/mjbommar/projects/personal/axeyum/.claude/worktrees/agent-a075a173892906668
A="$S/crates/axeyum-solver/src/auto.rs"
BASE="$W/bench-results/dispatch-decline-audit-20260913/refusal-propagation-baseline.json"
cp "$A" "$A.keep"

python3 - "$A" <<'PY'
import sys
p = sys.argv[1]
s = open(p).read()
old = """    let result = match crate::nra::check_with_nra(arena, &eliminated, &nra_config) {
        Ok(result) => result,
        Err(SolverError::Unsupported(message)) => {
            with_recorder(rec, |t| {
                t.record_declined("uf-nra", unsupported_decline(&message));
            });
            return Ok(None);
        }
        Err(other) => return Err(other),
    };"""
new = "    let result = crate::nra::check_with_nra(arena, &eliminated, &nra_config)?;"
assert s.count(old) == 1, f"anchor matched {s.count(old)} times"
open(p, 'w').write(s.replace(old, new))
print("re-introduced one propagation site")
PY

echo "--- ratchet on the MUTATED tree (must be non-zero) ---"
python3 "$W/scripts/enumerate-dispatch-refusal-propagation.py" \
  --root "$S/crates/axeyum-solver/src" --quiet --fail-on-new "$BASE"
rc=$?
echo "mutated-exit=$rc"
mv "$A.keep" "$A"

echo "--- ratchet on the RESTORED tree (must be zero) ---"
python3 "$W/scripts/enumerate-dispatch-refusal-propagation.py" \
  --root "$S/crates/axeyum-solver/src" --quiet --fail-on-new "$BASE"
echo "restored-exit=$?"
[ "$rc" -ne 0 ] || { echo "RATCHET IS VACUOUS -- it did not fire on a re-introduced site"; exit 1; }
echo "RATCHET-CONTROL-OK"
