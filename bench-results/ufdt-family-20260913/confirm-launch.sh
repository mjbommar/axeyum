#!/usr/bin/env bash
# Shard `confirm-moved.sh` across the physical cores the A/B chain is NOT using.
# The chain holds 1,9 / 3,11 / 5,13 / 6,14 on each of s5/s6/s7; this takes
# 2,10 and 4,12, so no two jobs of this lane share a physical core.
#
# Usage: confirm-launch.sh <moved-list> <tag>
set -eu
LIST="$1"; TAG="$2"
H=/nas3/data/axeyum/harness/ufdt-family
OUT="$H/confirm-$TAG"
mkdir -p "$OUT"
HOSTS=(s5 s6 s7)
CORES=("2,10" "4,12")
N=$(( ${#HOSTS[@]} * ${#CORES[@]} ))

rm -f "$OUT"/part.*.txt "$OUT"/part.*.tsv "$OUT"/part.*.log
awk -v n="$N" -v out="$OUT" '{ print > sprintf("%s/part.%02d.txt", out, NR % n) }' "$LIST"

s=0
for h in "${HOSTS[@]}"; do
  for c in "${CORES[@]}"; do
    pl=$(printf '%s/part.%02d.txt' "$OUT" "$s")
    po=$(printf '%s/part.%02d.tsv' "$OUT" "$s")
    if [ ! -f "$pl" ]; then s=$((s + 1)); continue; fi
    ssh -n -f -- "$h" "cd /tmp && nohup setsid bash $H/scripts/confirm-moved.sh \
        $pl $H/bin/smtcomp_cli-lever 1 '$c' $po > $OUT/part.$(printf %02d $s).log 2>&1 < /dev/null &"
    echo "LAUNCHED confirm $TAG part $s on $h cores $c ($(wc -l < "$pl") files)"
    s=$((s + 1))
  done
done
echo "CONFIRM-LAUNCH-OK $TAG $N parts"
