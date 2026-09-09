#!/usr/bin/env bash
# A/B one file list through the shipped ladder at N portfolio workers.
#
# Prints one TSV row per (file, repeat): workers, verdict, wall_ms, deciding
# route. The A and B arms are the SAME binary and differ only in
# `AXEYUM_PORTFOLIO_WORKERS`, so a difference cannot be a build difference --
# which is the confound an A/B across two checkouts always carries here.
#
# Both arms are run for each file back to back before moving on, so a drift in
# machine load lands on both rather than on whichever ran second. Load is
# printed at the start and end of every pass; a run whose load moved is
# advisory, not comparable, and the caller has to be able to see that.
set -uo pipefail

usage() {
    echo "usage: $0 <binary> <file-list> <timeout-ms> <repeats> <workers-b> [taskset-cpus]" >&2
    exit 2
}

[ $# -ge 5 ] || usage
BIN=$1
LIST=$2
TIMEOUT_MS=$3
REPEATS=$4
WORKERS_B=$5
CPUS=${6:-}

RUNNER=()
if [ -n "$CPUS" ]; then
    RUNNER=(taskset -c "$CPUS")
fi

# The outer wall must exceed the solver's own budget or the harness kills a run
# the solver was about to answer, and every such kill is scored as a loss.
OUTER_S=$(( TIMEOUT_MS / 1000 + 8 ))

printf 'load_start\t%s\n' "$(cut -d' ' -f1-3 /proc/loadavg)" >&2
printf 'file\tworkers\trepeat\tverdict\twall_ms\troute\n'

while IFS= read -r f; do
    [ -n "$f" ] || continue
    [ -f "$f" ] || { printf '%s\tNA\t0\tmissing\t0\tnone\n' "$f"; continue; }
    for r in $(seq 1 "$REPEATS"); do
        for w in 1 "$WORKERS_B"; do
            start=$(date +%s%N)
            out=$(AXEYUM_PORTFOLIO_WORKERS="$w" timeout "$OUTER_S" \
                  "${RUNNER[@]}" "$BIN" "$f" --timeout-ms "$TIMEOUT_MS" --trace 2>&1)
            rc=$?
            end=$(date +%s%N)
            wall=$(( (end - start) / 1000000 ))
            if [ "$rc" -ne 0 ]; then
                verdict="killed"
            else
                verdict=$(printf '%s\n' "$out" | grep -E '^(sat|unsat|unknown)$' | tail -1)
                [ -n "$verdict" ] || verdict="no-verdict"
            fi
            route=$(printf '%s\n' "$out" \
                    | grep -oE 'decided_by=[a-zA-Z0-9:_-]+' | tail -1 | cut -d= -f2)
            [ -n "$route" ] || route="none"
            printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$w" "$r" "$verdict" "$wall" "$route"
        done
    done
done < "$LIST"

printf 'load_end\t%s\n' "$(cut -d' ' -f1-3 /proc/loadavg)" >&2
