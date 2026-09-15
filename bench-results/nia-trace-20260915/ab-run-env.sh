#!/usr/bin/env bash
# Interleaved per-file A/B of ONE binary under two ENV SETTINGS, where the
# setting is a whole `VAR=VAL` list rather than one variable. Lane NIA-TRACE,
# ADR-2112.
#
# `ab-run-floor.sh` (and `derived-order`'s runner it came from) each hard-code
# ONE variable name. The ideal-ceiling probe moves THREE at once
# (`AXEYUM_MAX_IDEAL_{GENERATORS,ATOMS,INEQUALITIES}`), so this takes the
# assignment list as the arm.
#
# It keeps the refusal that matters: two arms with the SAME setting produce a
# perfect zero that looks exactly like agreement, so identical arms abort.
#
# Both arms run back to back on the SAME file on the SAME pinned core, and the
# arm order alternates per file, so ambient load cancels in the DIFFERENCE
# rather than landing on whichever arm ran second.
#
# usage: ab-run-env.sh <tag> <list> <out.tsv> <core> <bin> <envA> <envB> [budget_s]
#   envA / envB are space-separated `VAR=VAL` lists; use '' for "nothing set".
set -uo pipefail
TAG=${1:?tag}; LIST=${2:?list}; OUT=${3:?out}; PIN=${4:?core}; AX=${5:?binary}
ENV_A=${6?envA}; ENV_B=${7?envB}; BUDGET=${8:-24}
HEADROOM=16
VLIM=$((8 * 1024 * 1024))

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }
if [ "$ENV_A" = "$ENV_B" ]; then
    echo "ABORT $TAG: both arms set [$ENV_A]."
    echo "  Two identical arms make every number vacuous while looking exactly"
    echo "  like agreement. Name two different settings."
    exit 2
fi

HASH=$(sha256sum "$AX" | cut -d' ' -f1)

run_arm() {  # $1 = env assignment list (may be empty)
    local t0 t1 raw rc verdict
    t0=$(date +%s%N)
    # shellcheck disable=SC2086  # $1 is a deliberate word-split assignment list
    raw=$(env $1 timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>/dev/null)
    rc=$?
    t1=$(date +%s%N)
    verdict=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
    printf '%s\t%s\t%s' "${verdict:-none}" "$(( (t1 - t0) / 1000000 ))" "$rc"
}

printf 'file\tA\tA_ms\tA_rc\tB\tB_ms\tB_rc\tfirst\tstatus\n' > "$OUT"
n=0
while IFS= read -r f; do
    [ -n "$f" ] || continue
    n=$((n + 1))
    st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
    if [ $((n % 2)) -eq 1 ]; then
        first=A; a=$(run_arm "$ENV_A"); b=$(run_arm "$ENV_B")
    else
        first=B; b=$(run_arm "$ENV_B"); a=$(run_arm "$ENV_A")
    fi
    printf '%s\t%s\t%s\t%s\t%s\n' "$f" "$a" "$b" "$first" "${st:-none}" >> "$OUT"
    printf '%s: %d files\n' "$TAG" "$n" >&2
done < "$LIST"
echo "AB-DONE $TAG $n files -> $OUT  bin=$HASH A=[$ENV_A] B=[$ENV_B]"
