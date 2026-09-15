#!/usr/bin/env bash
# Shard the ADR-2100 interleaved A/B across s5/s6/s7, one PHYSICAL core pair per
# shard. Modelled on `bench-results/dt-exactness-20260913/launch-ab.sh`.
#
# Takes BOTH binaries rather than an arm value: the arms are two builds, and
# `ab-run.sh` refuses if they hash the same.
#
# Usage: launch-ab.sh <binA> <binB> <outdir> <budget_s> <div>:<list> [...]
set -eu
AX_A="$1"; AX_B="$2"; OUTDIR="$3"; BUDGET="$4"; shift 4
REMOTE=/nas3/data/axeyum/harness/route-ownership/scripts
read -r -a HOSTS <<< "${AB_HOSTS:-s5 s6 s7}"
read -r -a CORES <<< "${AB_CORES:-1,9 3,11 5,13 6,14}"
SHARDS=$(( ${#HOSTS[@]} * ${#CORES[@]} ))

mkdir -p "$OUTDIR" "$OUTDIR/lists"
for spec in "$@"; do
  DIV="${spec%%:*}"; LIST="${spec#*:}"
  rm -f "$OUTDIR"/lists/"$DIV".*.txt
  awk -v n="$SHARDS" -v div="$DIV" -v out="$OUTDIR/lists" \
    '{ print > sprintf("%s/%s.%02d.txt", out, div, NR % n) }' "$LIST"
done

for spec in "$@"; do
  DIV="${spec%%:*}"
  s=0
  for h in "${HOSTS[@]}"; do
    for c in "${CORES[@]}"; do
      sl=$(printf '%s/lists/%s.%02d.txt' "$OUTDIR" "$DIV" "$s")
      so=$(printf '%s/%s.shard%02d.tsv' "$OUTDIR" "$DIV" "$s")
      if [ -s "$so" ]; then echo "ABORT: $so already non-empty"; exit 2; fi
      if [ ! -f "$sl" ]; then s=$((s + 1)); continue; fi
      ssh -n -f -- "$h" "cd /tmp && nohup setsid bash $REMOTE/ab-run.sh \
            $DIV-$s $sl $so '$c' $AX_A $AX_B $BUDGET \
            > $OUTDIR/$DIV.shard$(printf %02d $s).log 2>&1 < /dev/null &"
      echo "LAUNCHED $DIV shard $s on $h cores $c ($(wc -l < "$sl") files)"
      s=$((s + 1))
    done
  done
done
echo "LAUNCH-OK $SHARDS shards"
