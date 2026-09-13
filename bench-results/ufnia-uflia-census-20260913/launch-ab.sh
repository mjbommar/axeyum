#!/usr/bin/env bash
# Shard an interleaved A/B (`ab-run.sh`) across s5/s6/s7, one PHYSICAL core per
# shard.  Same placement rules as `launch.sh`; see its header for why one
# division at a time.
#
# Usage: launch-ab.sh <arm-tag> <bin> <outdir> <budget_s> <arm-env-value> <div>:<list>
set -eu
ARM="$1"; BIN="$2"; OUTDIR="$3"; BUDGET="$4"; ARMVAL="$5"; shift 5
REMOTE=/nas3/data/axeyum/harness/ufnia-uflia/scripts
# Overridable so a second measurement can be placed on cores this lane is
# not already holding -- `check-core-collisions` exists because two of THIS
# lane's own shards on one physical core is the collision that actually
# happens, not a foreign job.
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
            $DIV-$s $sl $so '$c' $BIN $ARMVAL $BUDGET \
            > $OUTDIR/$DIV.shard$(printf %02d $s).log 2>&1 < /dev/null &"
      echo "LAUNCHED $ARM $DIV shard $s on $h cores $c ($(wc -l < "$sl") files)"
      s=$((s + 1))
    done
  done
done
echo "LAUNCH-OK $ARM $SHARDS shards  arm=AXEYUM_QUANT_EGRAPH_RESERVE=$ARMVAL"
