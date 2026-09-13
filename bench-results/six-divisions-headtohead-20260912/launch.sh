#!/usr/bin/env bash
# Stage the harness and launch the six divisions: two per box, in sequence,
# two modulo-interleaved shards each on DISTINCT physical cores (0,8) and
# (2,10) -- a Ryzen 7 7840HS is 8 physical cores with SMT siblings at +8, so
# those two pins do not share a core.
#
# Pairing: the likely-slow quantified division first on each box, so the
# expensive half of each box's work starts immediately rather than queueing
# behind a cheap one.
#
# Shards are NR%2 through the pinned list, so each shard spans the whole
# division; the merged TSV is re-ordered back into the pinned list's order, so
# the artifact does not encode the shard split.
set -eu
LANE="$(cd "$(dirname "$0")" && pwd)"
H=/nas3/data/axeyum/harness/six-divisions

mkdir -p "$H/lists" "$H/out"
cp "$LANE/shard-run.sh" "$LANE/chain-run.sh" "$LANE/census-run.sh" "$H/"
chmod +x "$H/shard-run.sh" "$H/chain-run.sh" "$H/census-run.sh"

for d in NRA QF_AUFLIA BV AUFLIA UFLIA LRA; do
  awk 'NR%2==1' "$LANE/../parity-lists/$d.txt" > "$H/lists/$d.s0"
  awk 'NR%2==0' "$LANE/../parity-lists/$d.txt" > "$H/lists/$d.s1"
  a=$(wc -l < "$H/lists/$d.s0"); b=$(wc -l < "$H/lists/$d.s1")
  [ $((a + b)) = 200 ] || { echo "ABORT: $d shards are $a + $b"; exit 2; }
done

launch() { # $1 host  $2 divA  $3 divB
  ssh -o BatchMode=yes "$1" \
    "nohup $H/chain-run.sh $2 $3 > $H/out/chain.$1.log 2>&1 & sleep 1; \
     echo launched $2,$3 on \$(hostname)"
}

launch s5 BV NRA
launch s6 UFLIA QF_AUFLIA
launch s7 AUFLIA LRA
