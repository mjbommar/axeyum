#!/usr/bin/env bash
# Re-runs the two `--lib` tests that failed in ADR-2112's full sweep, SERIALIZED
# and one at a time, with the width-floor lever explicitly UNSET.
#
# Both are wall-clock-bounded (`pathological_overbound_...` gives itself 5 s;
# `check_qf_uf_with_config_is_bounded_by_timeout`'s own comment records a ~50 s
# solve that flaked at 60 s on slower runners), and the sweep ran while six
# other lanes were building on this box. A load flake and a real regression look
# identical in the sweep's output, so this separates them: if they pass here,
# the sweep's failure was contention; if they fail here too, it is not.
#
# `env -u` on the lever matters. A test passing only under an ambient variable
# is a gate on one shell, and a test FAILING only under one is the same defect
# in reverse.
set -uo pipefail
cd -- "$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)" || exit 2

for t in auto::tests::pathological_overbound_stays_terminal_under_every_policy \
         euf_egraph::tests::check_qf_uf_with_config_is_bounded_by_timeout; do
    echo "=== RETEST $t ==="
    env -u AXEYUM_INT_BLAST_WIDTH_FLOOR \
        scripts/cargo-serialized.sh test -p axeyum-solver --lib --features full \
        -- --test-threads=1 --exact "$t" 2>&1 \
        | grep -E "^test result:|^test .* \.\.\.|panicked|^error" | head -8
    echo "=== END $t ==="
done
echo "RETEST-DONE"
