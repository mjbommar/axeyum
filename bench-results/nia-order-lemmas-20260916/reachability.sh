#!/usr/bin/env bash
# Does the armed arm's lemma pass ever RUN on the real corpus?
# Lane NIA-ORDER-LEMMAS, ADR-2136.
#
# WHY THIS RUNS BEFORE THE A/B. A lever that is wired, parses, and is never
# reached produces an A/B of perfect zeros that reads exactly like "the idea is
# worth nothing". ADR-2112 proved its own floor reached by making the lever
# value non-numeric and watching `config_lever.rs:124` panic -- that proves the
# lever is READ. It does not prove the code behind it EXECUTES. This does.
#
# The pass lives in the refinement loop's round >= 1, so it is reached only when
# round 0 returns a SPURIOUS `sat`: a round-0 `unsat` decides the file, and a
# round-0 `unknown` (the linear relaxation itself running out of budget) ends
# the loop. `AXEYUM_NIA_DEBUG` prints one line per round plus
# `[nia] order/monotone: built=N new=M` from `refine_with_order_and_monotone`,
# so each file gets classified from the trace rather than from its verdict.
#
# usage: reachability.sh <list> <out.tsv> <bin> [budget_s] [core]
set -uo pipefail
LIST=${1:?list}; OUT=${2:?out}; AX=${3:?binary}; BUDGET=${4:-24}; PIN=${5:-}
HEADROOM=16
VLIM=$((8 * 1024 * 1024))

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }

printf 'file\tverdict\trounds\tround0\tbuilt\tnew\tproducts\tmccormick\tsplits\n' > "$OUT"
n=0; reached=0
while IFS= read -r f; do
    [ -n "$f" ] || continue
    n=$((n + 1))
    if [ -n "$PIN" ]; then
        raw=$(AXEYUM_NIA_ORDER_LEMMAS=1 AXEYUM_NIA_DEBUG=1 \
              timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
              bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
              "$AX" "$f" 2>&1)
    else
        raw=$(AXEYUM_NIA_ORDER_LEMMAS=1 AXEYUM_NIA_DEBUG=1 \
              timeout $((BUDGET + HEADROOM)) \
              bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
              "$AX" "$f" 2>&1)
    fi
    verdict=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
    rounds=$(printf '%s\n' "$raw" | grep -cE '^\[nia\] round [0-9]+: ')
    round0=$(printf '%s\n' "$raw" | grep -m1 -oE '^\[nia\] round 0: Ok\("[a-z]+"\)' \
             | grep -oE '"[a-z]+"' | tr -d '"')
    built=$(printf '%s\n' "$raw" | grep -oE 'order/monotone: built=[0-9]+' \
            | grep -oE '[0-9]+' | paste -sd+ - | bc 2>/dev/null)
    newn=$(printf '%s\n' "$raw" | grep -oE 'order/monotone: built=[0-9]+ new=[0-9]+' \
           | grep -oE 'new=[0-9]+' | grep -oE '[0-9]+' | paste -sd+ - | bc 2>/dev/null)
    shape=$(printf '%s\n' "$raw" | grep -m1 -oE 'products=[0-9]+ mccormick=[0-9]+ splits=[0-9]+')
    prod=$(printf '%s' "$shape" | grep -oE 'products=[0-9]+' | grep -oE '[0-9]+')
    mcc=$(printf '%s' "$shape" | grep -oE 'mccormick=[0-9]+' | grep -oE '[0-9]+')
    spl=$(printf '%s' "$shape" | grep -oE 'splits=[0-9]+' | grep -oE '[0-9]+')
    [ -n "${built:-}" ] && [ "${built:-0}" -gt 0 ] && reached=$((reached + 1))
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$f" "${verdict:-none}" "$rounds" "${round0:-none}" "${built:-0}" \
        "${newn:-0}" "${prod:-}" "${mcc:-}" "${spl:-}" >> "$OUT"
    printf '%d/%d reached=%d %s\n' "$n" "$reached" "$reached" "${f##*/}" >&2
done < "$LIST"

echo "REACHABILITY $n files, $reached reached the lemma pass -> $OUT"
# The exit status depends on the finding: an arm that never runs is not a
# measurement of the idea, and a caller must not read it as one.
[ "$reached" -gt 0 ]
