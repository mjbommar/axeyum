#!/usr/bin/env bash
# Fans the 403-file 2026-09-05 loss population out over pinned slots on one host.
#
# Slots are `taskset`-pinned to disjoint core pairs and balanced by WORST-CASE
# cost (files x 24 s), not by file count: a loss list is mostly files that spend
# the whole budget, so file count is a bad proxy. The host is not idle -- the
# load average before and after is recorded per slot in `frames/`, because a
# budget-bounded verdict IS load-sensitive and a sweep that does not record its
# own contention cannot be compared to one that does.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
outdir="$here/.."
src="$outdir/../parity-losses-20260905"
mkdir -p "$outdir/sweep" "$outdir/frames"

# slot -> "cores:DIV[,DIV...]"
slots=(
  "0-1:QF_NIA"
  "2-3:QF_UFLIA"
  "4-5:QF_IDL"
  "6-7:QF_LRA"
  "8-9:QF_RDL,QF_BV"
  "10-11:QF_UF,QF_ABV"
  "12-13:UF,QF_LIA,QF_SLIA"
)

i=0
for spec in "${slots[@]}"; do
  cores="${spec%%:*}"
  divs="${spec#*:}"
  (
    echo "slot $i cores=$cores divs=$divs start $(date -Is) load=$(cut -d' ' -f1-3 /proc/loadavg)" \
      > "$outdir/frames/slot$i.frame"
    IFS=',' read -ra dl <<< "$divs"
    for d in "${dl[@]}"; do
      taskset -c "$cores" bash "$here/sweep.sh" "$src/$d.txt" "$d" "$outdir/sweep/$d.tsv"
      echo "  $d done $(date -Is) load=$(cut -d' ' -f1-3 /proc/loadavg)" \
        >> "$outdir/frames/slot$i.frame"
    done
    echo "slot $i end $(date -Is) load=$(cut -d' ' -f1-3 /proc/loadavg)" \
      >> "$outdir/frames/slot$i.frame"
  ) &
  i=$((i + 1))
done
wait
echo "all slots done $(date -Is)"
