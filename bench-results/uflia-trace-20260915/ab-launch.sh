#!/usr/bin/env bash
# UFLIA-TRACE -- launch the six-division A/B across this lane's pinned cores.
#
#   ab-launch.sh <valueB> <shardspec> [budget_s]
#
# The six divisions share the quantifier engine: UFLIA, UFNIA, AUFLIRA, UF,
# UFDTLIRA, AUFDTLIRA. Files are interleaved ACROSS divisions into the shards so
# no shard is one division's cost profile, and so a host anomaly lands on all six
# rather than on one.
#
# This lane owns s6 physical core pairs 5,13 and 6,14 and nothing else.
#
# Runs `ab-self-check.sh` FIRST and refuses on its exit status: a one-binary A/B
# in which the variable never arrives prints a perfect zero that reads exactly
# like agreement.
set -eu
VB="$1"; SHARDSPEC="$2"; BUDGET="${3:-24}"
HERE="$(cd "$(dirname "$0")" && pwd)"
LANE_ROOT="$(cd "$HERE/../.." && pwd)"
STAGE=/nas3/data/axeyum/harness/uflia-trace/stage
AX=${UT_AX:-/nas3/data/axeyum/harness/uflia-trace/bin/smtcomp_cli-lever}
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental
read -r -a SHARDS <<< "$SHARDSPEC"

bash "$HERE/ab-self-check.sh" "$AX" "$VB"

mkdir -p "$STAGE"
cp "$HERE/ab-run.sh" "$STAGE/"
chmod +x "$STAGE/ab-run.sh"
rm -f "$STAGE"/ab.shard*.list "$STAGE"/ab.shard*.tsv "$STAGE"/ab.shard*.log

# Interleave across divisions, then round-robin into shards.
: > "$STAGE/ab.all.list"
for d in UFLIA UFNIA AUFLIRA UF UFDTLIRA AUFDTLIRA; do
  awk -F'\t' -v d="$d" 'NR>1 && $3!="" {print $3}' \
    "$LANE_ROOT/bench-results/ledger/t1-$d-db31113fa.tsv" \
    | sort -u | awk -v d="$d" '{print d"\t"$0}' >> "$STAGE/ab.all.list"
done
awk -F'\t' '{n[$1]++; print n[$1]"\t"$1"\t"$2}' "$STAGE/ab.all.list" \
  | sort -k1,1n -k2,2 | cut -f3 > "$STAGE/ab.interleaved.list"

n=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  printf '%s/%s\n' "$CORPUS" "$f" >> "$STAGE/ab.shard$((n % ${#SHARDS[@]})).list"
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
