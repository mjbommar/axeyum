#!/usr/bin/env bash
# Stage the harness on /nas3 and launch the four A-divisions across s5/s6/s7.
#
# Two shards per box on DISTINCT physical cores.  The 8 GiB address-space cap is
# per run, so three concurrent shards can reach 24 GiB on a 26 GB box; two
# cannot.  s5/s6/s7 are Ryzen 7 7840HS: 8 physical cores, SMT siblings at +8, so
# pins 0 and 2 do not share a core.
#
# Shards are NR%2 through the pinned list, so each shard spans the whole
# division.
#
# Usage: ARM=<arm-name> [ARMS="axeyum z3 cvc5"] launch.sh <division>...
set -eu
LANE="$(cd "$(dirname "$0")" && pwd)"
H=/nas3/data/axeyum/harness/nested-array-ir
ARM="${ARM:?ARM must name a built arm (see build.sh)}"
ARMS="${ARMS:-axeyum z3 cvc5}"
RUNTAG="${RUNTAG:-$ARM}"

mkdir -p "$H/lists" "$H/out/$RUNTAG"
cp "$LANE/shard-run.sh" "$H/"
chmod +x "$H/shard-run.sh"

for d in "$@"; do
  awk 'NR%2==1' "$LANE/../parity-lists/$d.txt" > "$H/lists/$d.s0"
  awk 'NR%2==0' "$LANE/../parity-lists/$d.txt" > "$H/lists/$d.s1"
  a=$(wc -l < "$H/lists/$d.s0"); b=$(wc -l < "$H/lists/$d.s1")
  [ $((a + b)) = 200 ] || { echo "ABORT: $d shards are $a + $b"; exit 2; }
done
echo "lists staged: $*"
