#!/usr/bin/env bash
# Lane budget-discipline, step 3: how big is the tableau `lra::simplex_fallback`
# actually builds, and does it DECIDE when it is over `MAX_TABLEAU_CELLS`?
#
# `simplex::MAX_TABLEAU_CELLS` (4 000 000) is checked only in
# `Incremental::new`. `feasible` -- the constructor this route calls -- consults
# no cell bound at all and reached 360 million cells on a measured file. Adding
# the check changes DEFAULT admission, so the population it would refuse has to
# be measured before it is changed.
#
# Usage: cells-sweep.sh <list.txt> <binary> <out.tsv>
set -uo pipefail

LIST="$1"
BIN="$2"
OUT="$3"

printf '# binary %s sha256 %s\n' "$BIN" "$(sha256sum "$BIN" | cut -d' ' -f1)" > "$OUT"
printf '# host %s loadavg-at-start %s\n' "$(hostname -s)" "$(cut -d' ' -f1-3 /proc/loadavg)" >> "$OUT"
printf 'file\twall_ms\tverdict\tcells_lines\n' >> "$OUT"

export AXEYUM_LRA_CELLS=1
while IFS= read -r f; do
  [ -z "$f" ] && continue
  start=$(date +%s%N)
  raw=$(ulimit -v 8388608; timeout 40 "$BIN" --trace --timeout-ms 24000 --memory-limit-mb 8192 "$f" 2>&1)
  end=$(date +%s%N)
  wall=$(( (end - start) / 1000000 ))
  verdict=$(printf '%s\n' "$raw" | grep -v '^;' | tail -1)
  cells=$(printf '%s\n' "$raw" | grep '^; lra-simplex-fallback ' | tr '\n' '|')
  printf '%s\t%s\t%s\t%s\n' "$f" "$wall" "$verdict" "$cells" >> "$OUT"
done < "$LIST"
echo "CELLS_SWEEP_COMPLETE $OUT"
