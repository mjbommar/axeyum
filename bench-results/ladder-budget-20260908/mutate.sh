#!/usr/bin/env bash
# Lane budget-discipline: does each guard actually fail when the thing it guards
# is removed?
#
# Two mutations, applied one at a time in this ISOLATED worktree with a trap
# that restores the file whatever happens. Each asserts its own anchor is
# present first, so a green run cannot come from a mutation that never applied.
# The whole `--lib --features full` suite runs, not a filtered subset, because
# "exactly one test dies" is a claim about every test there is.
#
#   reserve  -- ABV_ONLINE_SLICE stops reserving: the online route takes the
#               whole clock again.
#   handroll -- a fifth hand-rolled divisor appears in the file (the exact
#               arithmetic the policy replaced, written by hand).
#
# Usage: mutate.sh reserve|handroll
set -uo pipefail
cd "$(dirname "$0")/.."

WHICH="${1:?usage: mutate.sh reserve|handroll}"
F=crates/axeyum-solver/src/auto.rs
BAK=.lane-budget-discipline/auto.rs.premutation
cp "$F" "$BAK"
restore() { cp "$BAK" "$F"; touch "$F"; }
trap restore EXIT

python3 - "$WHICH" <<'PY' || exit 1
import sys

which = sys.argv[1]
path = 'crates/axeyum-solver/src/auto.rs'
text = open(path, encoding='utf-8').read()

if which == 'reserve':
    old = """const ABV_ONLINE_SLICE: LadderSlice =
    LadderSlice::all_but_reserve("abv-online-cdclt", ABV_ONLINE_LADDER_RESERVE_SHARE);"""
    new = """const ABV_ONLINE_SLICE: LadderSlice =
    LadderSlice::all_but_reserve("abv-online-cdclt", u32::MAX);"""
elif which == 'handroll':
    old = """fn int_real_relax_budget(config: &SolverConfig) -> SolverConfig {
    INT_REAL_RELAX_SLICE.apply(config, config.timeout)
}"""
    new = """fn int_real_relax_budget(config: &SolverConfig) -> SolverConfig {
    let mut sliced = config.clone();
    if let Some(t) = config.timeout {
        sliced.timeout = Some(t / 6);
    }
    sliced
}"""
elif which == 'inversion':
    # The bug exactly as it stood: a share that rounds to zero returns the
    # caller's config UNCHANGED, i.e. the route asked for a sixth of the clock
    # gets all of it.
    old = """fn int_real_relax_budget(config: &SolverConfig) -> SolverConfig {
    INT_REAL_RELAX_SLICE.apply(config, config.timeout)
}"""
    new = """fn int_real_relax_budget(config: &SolverConfig) -> SolverConfig {
    let Some(timeout) = config.timeout else {
        return config.clone();
    };
    let share = timeout / INT_REAL_RELAX_BUDGET_SHARE;
    if share.is_zero() {
        return config.clone();
    }
    config.clone().with_timeout(share)
}"""
else:
    raise SystemExit(f'unknown mutation {which}')

assert old in text, (
    'MUTATION ANCHOR NOT FOUND -- the mutation did not apply, '
    'so a green run proves nothing'
)
open(path, 'w', encoding='utf-8').write(text.replace(old, new))
print(f'mutation {which} applied')
PY

touch "$F"
./scripts/cargo-serialized.sh test -p axeyum-solver --lib --features full -- --test-threads=4 \
  2>&1 | grep -E "^test result|FAILED|^failures:$|^    [a-z_:]+$" | tail -30
