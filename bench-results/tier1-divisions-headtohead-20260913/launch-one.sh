#!/usr/bin/env bash
# Launch ONE division's board on a named host and a named pair of physical
# cores, outside the `launch.sh` chains.
#
# Seven divisions over three boxes does not divide, and the chains are not
# equally fast: UFNIA ran at roughly 1.7 min per file where AUFLIRA ran at
# 0.1 s for most of its rows, so a static 3/2/2 split leaves a box idle for
# hours while another is still on its first division.  This dispatches the
# remainder onto whatever cores are actually free.
#
# It refuses if the division's output already exists, because a second run of a
# division already measured would silently replace a committed row set with one
# taken under different conditions.
#
# Check `out/loadframe.tsv`'s `foreign_cores` column before choosing cores, and
# do not reuse a core another lane or another shard of this board holds.
#
# Usage: launch-one.sh <host> <DIV> <coresA> <coresB>
set -eu
H=/nas3/data/axeyum/harness/tier1-divisions
HOST="$1"; DIV="$2"; CA="$3"; CB="$4"

for s in s0 s1; do
  [ -f "$H/lists/$DIV.$s" ] || { echo "ABORT: $H/lists/$DIV.$s missing"; exit 2; }
  if [ -s "$H/out/$DIV.$s.tsv" ]; then
    echo "ABORT: $H/out/$DIV.$s.tsv already has rows -- refusing to re-measure"
    exit 2
  fi
done

ssh -o BatchMode=yes "$HOST" \
  "nohup bash -c '\"$H/shard-run.sh\" \"$DIV.s0\" \"$H/lists/$DIV.s0\" \"$H/out/$DIV.s0.tsv\" $CA > $H/out/$DIV.s0.log 2>&1 &
                  \"$H/shard-run.sh\" \"$DIV.s1\" \"$H/lists/$DIV.s1\" \"$H/out/$DIV.s1.tsv\" $CB > $H/out/$DIV.s1.log 2>&1 &
                  wait' > /dev/null 2>&1 & sleep 1; echo launched $DIV on \$(hostname) cores $CA and $CB"
