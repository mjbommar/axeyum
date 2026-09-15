#!/usr/bin/env bash
# CORE-SELECT -- assemble a sharded run's TSVs into ONE committed artifact.
#
#   collect.sh <tag> <out.tsv> [expected-rows]
#
# Checks the shard COUNT and the row COUNT, and refuses when a shard is missing
# or short: a collector that concatenates whatever is there reports a partial
# sweep as a complete one, and nothing downstream can tell the difference.
# Exit status depends on the finding.
set -u
TAG="$1"; OUT="$2"; EXPECT="${3:-0}"
STAGE=/nas3/data/axeyum/harness/core-select/stage
shopt -s nullglob
files=("$STAGE/$TAG".shard*.tsv)
lists=("$STAGE/$TAG".shard*.list)
if [ "${#files[@]}" -eq 0 ]; then
  echo "ABORT: no shard TSVs for tag $TAG"; exit 2
fi
if [ "${#files[@]}" -ne "${#lists[@]}" ]; then
  echo "ABORT: $TAG has ${#lists[@]} shard lists but ${#files[@]} shard TSVs"
  exit 3
fi
head -1 "${files[0]}" > "$OUT"
tail -n +2 -q "${files[@]}" | LC_ALL=C sort >> "$OUT"
rows=$(( $(wc -l < "$OUT") - 1 ))
want=0
for l in "${lists[@]}"; do want=$(( want + $(grep -c . "$l") )); done
echo "$TAG: shards=${#files[@]} rows=$rows listed=$want out=$OUT"
rc=0
if [ "$rows" -ne "$want" ]; then
  echo "SHORT: $((want - rows)) listed file(s) produced no row"
  rc=4
fi
if [ "$EXPECT" -gt 0 ] && [ "$rows" -ne "$EXPECT" ]; then
  echo "UNEXPECTED: wanted $EXPECT rows, got $rows"
  rc=5
fi
# A duplicate means two shards censused the same file -- the exact failure the
# weighted up-front partition exists to prevent, so it is checked rather than
# assumed away.
dup=$(cut -f1 "$OUT" | tail -n +2 | LC_ALL=C sort | uniq -d | head -5)
if [ -n "$dup" ]; then
  echo "DUPLICATE rows (two shards took the same file):"
  printf '  %s\n' $dup
  rc=6
fi
exit $rc
