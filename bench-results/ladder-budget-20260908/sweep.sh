#!/usr/bin/env bash
# Lane budget-discipline: run a committed list through smtcomp_cli --trace and
# record, per file, the verdict, wall clock, the ADR-1760 route-attribution line
# and the full trail.
#
# Usage: sweep.sh <list.txt> <binary> <out.tsv> [abv-reserve-policy]
# `policy` is exported as AXEYUM_ABV_ONLINE_RESERVE (off|on); omitted leaves the
# binary's shipped default (on).
# Protocol: 24 s wall, 8 GiB `ulimit -v`, one file at a time, matching
# scripts/parity-run.sh so the numbers are comparable to the ledger.
set -uo pipefail

LIST="$1"
BIN="$2"
OUT="$3"
if [ "$#" -ge 4 ]; then
  export AXEYUM_ABV_ONLINE_RESERVE="$4"
fi

# The binary's digest FIRST: a sweep that reads a binary while a build is
# writing it silently changes solver mid-run, and nothing in the TSV would say
# so. Pass a pinned COPY, and this line is what proves you did.
printf '# binary %s sha256 %s\n' "$BIN" "$(sha256sum "$BIN" | cut -d' ' -f1)" > "$OUT"
printf '# policy AXEYUM_ABV_ONLINE_RESERVE=%s\n' "${AXEYUM_ABV_ONLINE_RESERVE:-<default>}" >> "$OUT"
printf '# host %s loadavg-at-start %s\n' "$(hostname -s)" "$(cut -d' ' -f1-3 /proc/loadavg)" >> "$OUT"
printf 'file\twall_ms\tverdict\troute_line\n' >> "$OUT"

while IFS= read -r f; do
  [ -z "$f" ] && continue
  start=$(date +%s%N)
  raw=$(ulimit -v 8388608; timeout 40 "$BIN" --trace --timeout-ms 24000 --memory-limit-mb 8192 "$f" 2>&1)
  end=$(date +%s%N)
  wall=$(( (end - start) / 1000000 ))
  verdict=$(printf '%s\n' "$raw" | grep -v '^;' | tail -1)
  route=$(printf '%s\n' "$raw" | grep '^; route ' | head -1)
  printf '%s\t%s\t%s\t%s\n' "$f" "$wall" "$verdict" "$route" >> "$OUT"
done < "$LIST"
echo "SWEEP_COMPLETE $OUT"
