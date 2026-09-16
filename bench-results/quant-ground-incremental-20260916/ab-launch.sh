#!/usr/bin/env bash
# QUANT-GROUND-INCREMENTAL -- launch the six-division A/B across this lane's pinned cores.
#
#   ab-launch.sh <valueB> <shardspec> [budget_s] [stage]
#
# The six divisions share the quantifier engine: UFLIA, UFNIA, AUFLIRA, UF,
# UFDTLIRA, AUFDTLIRA. Files are interleaved ACROSS divisions into the shards so
# no shard is one division's cost profile, a host anomaly lands on all six rather
# than on one, and -- the reason that matters most -- a sweep read before it
# finishes is a fair SAMPLE of all six rather than a prefix of one. A parity list
# read as a prefix has published two false nulls in this repository.
#
# ONE process per shard and one shard per PHYSICAL CORE PAIR. ADR-2103 measured
# 9x oversubscription collapsing BOTH arms, which is a way to report a null that
# says nothing about the lever.
#
# This lane owns s6 physical core pairs 1,9 / 3,11 / 5,13 / 6,14 and nothing else.
#
# Runs `ab-self-check.sh` FIRST and refuses on its exit status.
set -eu
VB="$1"; SHARDSPEC="$2"; BUDGET="${3:-24}"
HERE="$(cd "$(dirname "$0")" && pwd)"
LANE_ROOT="$(cd "$HERE/../.." && pwd)"
STAGE="${4:-/nas3/data/axeyum/harness/quant-ground-incremental/stage}"
AX=${QGI_AX:-/nas3/data/axeyum/harness/quant-ground-incremental/bin/smtcomp_cli-lane}
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental
LIST_SRC="${QGI_LIST:-}"
read -r -a SHARDS <<< "$SHARDSPEC"

bash "$HERE/ab-self-check.sh" "$AX" "$VB"

mkdir -p "$STAGE"
cp "$HERE/ab-run.sh" "$STAGE/"
chmod +x "$STAGE/ab-run.sh"
rm -f "$STAGE"/ab.shard*.list "$STAGE"/ab.shard*.tsv "$STAGE"/ab.shard*.log

if [ -n "$LIST_SRC" ]; then
  # A caller-supplied list (the held-out draw) is already interleaved by its
  # own construction; take it verbatim so the draw is not silently reordered.
  cp "$LIST_SRC" "$STAGE/ab.interleaved.list"
else
  : > "$STAGE/ab.all.list"
  for d in UFLIA UFNIA AUFLIRA UF UFDTLIRA AUFDTLIRA; do
    awk -F'\t' -v d="$d" 'NR>1 && $3!="" {print $3}' \
      "$LANE_ROOT/bench-results/ledger/t1-$d-db31113fa.tsv" \
      | sort -u | awk -v d="$d" '{print d"\t"$0}' >> "$STAGE/ab.all.list"
  done
  awk -F'\t' '{n[$1]++; print n[$1]"\t"$1"\t"$2}' "$STAGE/ab.all.list" \
    | sort -k1,1n -k2,2 | cut -f3 > "$STAGE/ab.interleaved.list"
fi

n=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  case "$f" in
    /*) printf '%s\n' "$f" >> "$STAGE/ab.shard$((n % ${#SHARDS[@]})).list" ;;
    *)  printf '%s/%s\n' "$CORPUS" "$f" >> "$STAGE/ab.shard$((n % ${#SHARDS[@]})).list" ;;
  esac
  n=$((n + 1))
done < "$STAGE/ab.interleaved.list"
echo "ab: $n files over ${#SHARDS[@]} shards (${SHARDS[*]}) budget=${BUDGET}s valueB=$VB"

i=0
for sh in "${SHARDS[@]}"; do
  host="${sh%%:*}"; core="${sh##*:}"
  L="$STAGE/ab.shard$i.list"
  if [ -f "$L" ]; then
    ssh -o BatchMode=yes "$host" \
      "nohup setsid $STAGE/ab-run.sh shard$i $L $STAGE/ab.shard$i.tsv $core $AX $VB $BUDGET \
         > $STAGE/ab.shard$i.log 2>&1 < /dev/null &" >/dev/null 2>&1
    echo "  launched ab shard$i on $host core $core ($(wc -l < "$L") files)"
  fi
  i=$((i + 1))
done
echo "ab: artifacts at $STAGE/ab.shard*.tsv"
