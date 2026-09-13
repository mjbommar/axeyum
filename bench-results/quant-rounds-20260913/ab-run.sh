#!/usr/bin/env bash
# Interleaved per-file A/B over a pinned list.
#
# Both arms run BACK TO BACK on the SAME pinned core, and the arm that goes
# FIRST alternates per file.  Ambient load then cancels in the difference
# rather than landing on whichever arm happened to run during a build -- the
# discipline `board-six` used for three solvers and the reason a 1-2 file
# absolute difference is noise while the per-file pairing is not.
#
# Arm A is the shipped default: NO environment set at all, so it is the binary
# as shipped rather than a value someone typed.  Arm B is whatever VAR=VAL
# pairs are passed.
#
# Usage: ab-run.sh <tag> <list> <out.tsv> <core> VAR=VAL [VAR=VAL ...]
set -u
BUDGET=24
HEADROOM=16
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; shift 4
[ "$#" -ge 1 ] || { echo "ABORT $TAG: arm B needs at least one VAR=VAL"; exit 2; }
AX="${AX:-/nas3/data/axeyum/harness/quant-rounds/bin/smtcomp_cli}"
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }

# One solve.  `env -u` on every lever this lane can set, so arm A is provably
# the shipped arm even if the caller's shell already exports one of them --
# the failure mode where an "A/B" measures arm B twice.
solve() {
  local file="$1"; shift
  timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
    env -u AXEYUM_QINST_ROUNDS -u AXEYUM_QINST_CADENCE -u AXEYUM_QINST_ROUND_HEADROOM \
        -u AXEYUM_QINST_GROUND "$@" \
    bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
    "$AX" "$file" 2>/dev/null
}

classify() {
  case "$1" in
    *"did not refute within the round budget"*)           echo ROUND ;;
    *"reached fixpoint without refuting after"*)          echo SHAPE ;;
    *"could not fit another round with growth headroom"*) echo CLOCK ;;
    "")                                                   echo NOGIVEUP ;;
    *)                                                    echo OTHER ;;
  esac
}

printf 'file\ta_verdict\ta_ms\ta_kind\tb_verdict\tb_ms\tb_kind\tfirst\ta_giveup\tb_giveup\n' > "$OUT"
i=0
while read -r f; do
  i=$((i + 1))
  if [ $((i % 2)) -eq 1 ]; then first=A; else first=B; fi

  run_a() {
    t0=$(date +%s%N); araw=$(solve "$f"); t1=$(date +%s%N)
    ams=$(( (t1 - t0) / 1000000 ))
  }
  run_b() {
    t0=$(date +%s%N); braw=$(solve "$f" "$@"); t1=$(date +%s%N)
    bms=$(( (t1 - t0) / 1000000 ))
  }

  if [ "$first" = A ]; then run_a; run_b "$@"; else run_b "$@"; run_a; fi

  av=$(printf '%s\n' "$araw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  bv=$(printf '%s\n' "$braw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  ag=$(printf '%s\n' "$araw" | grep -m1 -oE 'give-up kind=[^ ]+ detail=.*' | tr '\t' ' ')
  bg=$(printf '%s\n' "$braw" | grep -m1 -oE 'give-up kind=[^ ]+ detail=.*' | tr '\t' ' ')

  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "${f#"$CORPUS"}" "${av:-none}" "$ams" "$(classify "$ag")" \
    "${bv:-none}" "$bms" "$(classify "$bg")" "$first" \
    "${ag:-none}" "${bg:-none}" >> "$OUT"
done < "$LIST"
echo "AB-DONE $TAG $(($(wc -l < "$OUT") - 1)) rows"
