#!/usr/bin/env bash
# WHICH of the instantiation loop's three stopping conditions actually fires.
#
# ADR-1950 ranked `e-matching instantiation did not refute within the round
# budget` as 177 of 390 winnable files and classified it `ROUND` -- from the
# STRING, because the string was all a census could read.  All three exits of
# the loop emitted that one string (`qinst_egraph.rs`'s own dump label for the
# point is `"fixpoint-or-break"`), so the classification could not be checked.
#
# This run uses the split detail (`InstantiationLoopExit`) to classify each row
# by what stopped it:
#
#   ROUND  ... did not refute within the round budget        -> the ceiling
#   SHAPE  ... reached fixpoint without refuting after N ...  -> nothing left to admit
#   CLOCK  ... could not fit another round with growth ...    -> the wall clock
#
# Same 24 s / 8 GiB / pinned-core envelope as the board this population came
# from, so a row here is comparable to the row it came from.
#
# Usage: exit-census.sh <tag> <list> <out.tsv> <core> [VAR=VAL ...]
set -u
BUDGET=24
HEADROOM=16
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; shift 4
AX="${AX:-/nas3/data/axeyum/harness/quant-rounds/bin/smtcomp_cli}"
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }

printf 'file\tverdict\trc\twall_ms\texit_kind\trounds\ttotal_ms\tgiveup\n' > "$OUT"
while read -r f; do
  t0=$(date +%s%N)
  raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          env "$@" bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>/dev/null)
  rc=$?
  t1=$(date +%s%N)
  wall=$(( (t1 - t0) / 1000000 ))
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  g=$(printf '%s\n' "$raw" | grep -m1 -oE 'give-up kind=[^ ]+ detail=.*' | tr '\t' ' ')
  tms=$(printf '%s\n' "$raw" | grep -m1 -oE '; (partial )?route decided_by=.*' \
          | grep -oE 'total_ms=[0-9]+' | head -1 | cut -d= -f2)
  # The exit kind is derived from the detail, never assumed: a row whose detail
  # matches none of the three prints UNMATCHED rather than defaulting into one
  # of them, because a silent default is how the merged bucket happened.
  case "$g" in
    *"did not refute within the round budget"*)              k=ROUND;  r=ceiling ;;
    *"reached fixpoint without refuting after"*)             k=SHAPE;  r=$(printf '%s\n' "$g" | grep -oE 'after [0-9]+ rounds' | grep -oE '[0-9]+') ;;
    *"could not fit another round with growth headroom"*)    k=CLOCK;  r=$(printf '%s\n' "$g" | grep -oE 'after [0-9]+ rounds' | grep -oE '[0-9]+') ;;
    "")                                                      k=NOGIVEUP; r=na ;;
    *)                                                       k=OTHER;  r=na ;;
  esac
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "${f#"$CORPUS"}" "${v:-none}" "$rc" "$wall" "$k" "${r:-na}" "${tms:-na}" "${g:-none}" >> "$OUT"
done < "$LIST"
echo "EXIT-CENSUS-DONE $TAG $(($(wc -l < "$OUT") - 1)) rows"
