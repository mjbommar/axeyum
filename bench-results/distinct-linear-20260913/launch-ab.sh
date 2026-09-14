#!/usr/bin/env bash
# Shard an interleaved A/B (`ab-run.sh`) across s5/s6/s7, one PHYSICAL core-pair
# per shard.
#
# This lane takes SIX of the twelve available pinned core pairs: `1,9` and
# `3,11` on each of s5, s6 and s7. `5,13` and `6,14` are left free on all three.
#
# The arm VALUE is a parameter (`on`, `mutant:vacuous`, `mutant:shared`) because
# the mutation control needs the same interleaved protocol as the real arm. The
# arm POLARITY is not a parameter -- `ab-run.sh` hardcodes `base` as the unset
# environment, which is the shipped behaviour for this lever.
#
# Usage: launch-ab.sh <bin> <outdir> <budget_s> <arm_value> <tag>:<list> [...]
set -eu
BIN="$1"; OUTDIR="$2"; BUDGET="$3"; ARMVAL="$4"; shift 4
REMOTE=/nas3/data/axeyum/harness/distinct-linear/scripts
read -r -a HOSTS <<< "${AB_HOSTS:-s5 s6 s7}"
read -r -a CORES <<< "${AB_CORES:-1,9 3,11}"
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
            $DIV-$s $sl $so '$c' $BIN $BUDGET $ARMVAL \
            > $OUTDIR/$DIV.shard$(printf %02d $s).log 2>&1 < /dev/null &"
      echo "LAUNCHED $DIV shard $s on $h cores $c ($(wc -l < "$sl") files)"
      s=$((s + 1))
    done
  done
done
echo "LAUNCH-OK $SHARDS shards  base=unset(shipped)  arm=AXEYUM_DISTINCT_LINEAR=$ARMVAL"
