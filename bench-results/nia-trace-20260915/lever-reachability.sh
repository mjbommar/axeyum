#!/usr/bin/env bash
# Does `AXEYUM_INT_BLAST_WIDTH_FLOOR` reach anything at all? (lane NIA-TRACE,
# ADR-2112)
#
# An A/B whose lever is never read reports `0 losses, 0 gains, 0 flips` and
# looks exactly like a lever that is safe and worthless. It is the same shape
# as a gate that runs zero tests and exits 0. So before the A/B runs, this
# establishes that the two arms are doing different work -- by TIME on files
# whose ladder has many inadmissible rungs, where the armed arm must be no
# slower and should be measurably faster.
#
# It is a reachability control, not a benchmark: it reports the pair per file
# and says nothing about whether the saving is worth shipping.
#
# usage: lever-reachability.sh <axeyum-binary> <paths-file> <core> [budget_s] [repeats]
set -uo pipefail

AX=${1:?axeyum binary}
LIST=${2:?paths file}
CORE=${3:?core}
BUDGET=${4:-24}
REPEATS=${5:-3}
VLIM=$((8 * 1024 * 1024))

[ -x "$AX" ] || { echo "ABORT: $AX is not executable"; exit 2; }

run_arm() {  # $1 = lever value, $2 = file
    local t0 t1 raw verdict
    t0=$(date +%s%N)
    raw=$(AXEYUM_INT_BLAST_WIDTH_FLOOR="$1" timeout $((BUDGET + 16)) taskset -c "$CORE" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$2" 2>/dev/null)
    t1=$(date +%s%N)
    verdict=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
    printf '%s\t%s' "${verdict:-none}" "$(( (t1 - t0) / 1000000 ))"
}

printf 'file\trepeat\tdisarmed\tdisarmed_ms\tarmed\tarmed_ms\n'
differing=0
compared=0
while IFS= read -r file; do
    [ -n "$file" ] || continue
    for r in $(seq 1 "$REPEATS"); do
        # Alternate which arm runs first, so a warm page cache lands on both.
        if [ $((r % 2)) -eq 1 ]; then
            a=$(run_arm 0 "$file"); b=$(run_arm 1 "$file")
        else
            b=$(run_arm 1 "$file"); a=$(run_arm 0 "$file")
        fi
        printf '%s\t%s\t%s\t%s\n' "${file##*/}" "$r" "$a" "$b"
        compared=$((compared + 1))
        a_ms=${a#*$'\t'}; b_ms=${b#*$'\t'}
        # "Different work" = the armed arm finished at least 5 % sooner.
        if [ "$a_ms" -gt 0 ] && [ $(( (a_ms - b_ms) * 100 / a_ms )) -ge 5 ]; then
            differing=$((differing + 1))
        fi
    done
done < "$LIST"

printf 'REACHABILITY: %d of %d paired runs show the armed arm at least 5%% faster\n' \
    "$differing" "$compared"
if [ "$differing" -eq 0 ]; then
    printf 'THE LEVER MAY NOT BE REACHED. An A/B on this population would report\n'
    printf 'zero movement whether the lever works or not, and would prove nothing.\n'
    exit 1
fi
