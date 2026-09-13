#!/usr/bin/env bash
# Everything that happens to a division once its 200 rows are in: merge the
# shards back into pinned-list order, derive the winnable set, launch the
# blocker census over ALL of it, and launch the 600 s re-check over any verdict
# nothing confirmed.
#
# One script because the three steps have an order and a shared precondition,
# and doing them by hand is how this lane started the FP board on cores a census
# shard was still holding.  `merge-division.py` ABORTS unless the shards cover
# the pinned 200 exactly, so this cannot proceed on a partial division.
#
# Usage: finish-division.sh <DIV> <host> <censusCoresA> <censusCoresB> [<confirmCores>]
set -eu
LANE="$(cd "$(dirname "$0")" && pwd)"
H=/nas3/data/axeyum/harness/tier1-divisions
DIV="$1"; HOST="$2"; CA="$3"; CB="$4"; CC="${5:-}"

echo "== merge $DIV"
python3 "$LANE/merge-division.py" "$DIV"

echo "== census $DIV on $HOST cores $CA $CB"
if [ -s "$LANE/winnable/$DIV.txt" ]; then
  bash "$LANE/census-launch.sh" "$HOST" "$DIV" "$CA" "$CB"
else
  echo "   winnable set is EMPTY -- no census to run (this is a result, not a skip)"
fi

if [ -n "$CC" ]; then
  # Rows where WE decided and neither `:status` nor either reference could
  # speak to it.  ADR-1957: those must not be counted in a zero.
  n=$(awk -F'\t' 'NR>1 && ($2=="sat"||$2=="unsat") && $11!="sat" && $11!="unsat" \
        && $5!="sat" && $5!="unsat" && $8!="sat" && $8!="unsat"' \
      "$LANE/$DIV.tsv" | wc -l)
  if [ "$n" = 0 ]; then
    echo "== confirm $DIV: 0 unchecked verdicts -- nothing to re-check"
  else
    echo "== confirm $DIV: $n unchecked verdict(s) on $HOST core $CC"
    mkdir -p "$H/boards"
    cp "$LANE/$DIV.tsv" "$H/boards/"
    ssh -o BatchMode=yes "$HOST" \
      "cd $H && nohup ./confirm-unchecked.sh out/confirm-$DIV.tsv $CC boards/$DIV.tsv \
       > out/confirm-$DIV.log 2>&1 & sleep 1; echo launched confirm-$DIV"
  fi
fi
echo "FINISH-DISPATCHED $DIV"
