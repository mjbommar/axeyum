#!/usr/bin/env bash
# Sweep the instantiation-round ceiling, do not toggle it.
#
# ADR-1945's QF_UFBV sweep found +31/+44/+45 at 2x/4x/8x and FLAT after 4x, and
# that shape -- not the single 8x number -- is what decided what shipped.  A
# toggle cannot tell "the cap is not binding" from "the cap is binding and 8x is
# not enough".
#
# Arms: the shipped 512, then 2x, 4x, 8x.  All four run BACK TO BACK on the SAME
# pinned core for one file before any arm sees the next file, and the arm ORDER
# ROTATES per file (arm i goes first on file i mod 4), so ambient load cannot
# land on one arm.
#
# Usage: sweep-run.sh <tag> <list> <out.tsv> <core>
set -u
BUDGET=24
HEADROOM=16
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"
AX="${AX:-/nas3/data/axeyum/harness/quant-rounds/bin/smtcomp_cli}"
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/
ARMS=(shipped 1024 2048 4096)

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }

# `env -u` every lever this lane owns on EVERY arm, so the shipped arm is the
# shipped binary even if the caller's shell exports one -- the failure where an
# A/B measures arm B twice.
solve() {
  local arm="$1" file="$2"
  local -a pre=(env -u AXEYUM_QINST_ROUNDS -u AXEYUM_QINST_CADENCE
                -u AXEYUM_QINST_ROUND_HEADROOM -u AXEYUM_QINST_GROUND)
  [ "$arm" = shipped ] || pre+=("AXEYUM_QINST_ROUNDS=$arm")
  timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" "${pre[@]}" \
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

hdr='file\tfirst_arm'
for a in "${ARMS[@]}"; do hdr="$hdr\t${a}_verdict\t${a}_ms\t${a}_kind"; done
printf "$hdr\n" > "$OUT"

i=0
while read -r f; do
  rot=$((i % ${#ARMS[@]}))
  row="${f#"$CORPUS"}"$'\t'"${ARMS[$rot]}"
  declare -A V M K
  for j in 0 1 2 3; do
    a="${ARMS[$(( (rot + j) % ${#ARMS[@]} ))]}"
    t0=$(date +%s%N); raw=$(solve "$a" "$f"); t1=$(date +%s%N)
    M[$a]=$(( (t1 - t0) / 1000000 ))
    V[$a]=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
    g=$(printf '%s\n' "$raw" | grep -m1 -oE 'give-up kind=[^ ]+ detail=.*')
    K[$a]=$(classify "$g")
  done
  for a in "${ARMS[@]}"; do
    row="$row"$'\t'"${V[$a]:-none}"$'\t'"${M[$a]}"$'\t'"${K[$a]}"
  done
  printf '%s\n' "$row" >> "$OUT"
  i=$((i + 1))
done < "$LIST"
echo "SWEEP-DONE $TAG $(($(wc -l < "$OUT") - 1)) rows"
