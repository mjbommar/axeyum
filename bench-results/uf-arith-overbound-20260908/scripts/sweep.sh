#!/usr/bin/env bash
# Lane euf-driver-mbtc: run a committed loss list through smtcomp_cli --trace and
# record, per file, the verdict, wall clock, the ADR-1760 route-attribution line
# and the full trail.
#
# Usage: sweep.sh <list.txt> <binary> <out.tsv> [policy]
# `policy` is exported as AXEYUM_UF_ARITH_OVERBOUND (terminal|probe|skip);
# omitted leaves the binary's shipped default.
# Protocol: 24s wall, 8 GiB `ulimit -v`, one file at a time (matches
# scripts/parity-run.sh so the numbers are comparable to the ledger).
set -uo pipefail

LIST="$1"
BIN="$2"
OUT="$3"
if [ "$#" -ge 4 ]; then
  export AXEYUM_UF_ARITH_OVERBOUND="$4"
fi

# Record the binary's digest FIRST. A sweep that reads `target/release/...`
# while a build is running silently changes solver mid-run: the first version of
# this lane's baseline had rows 1-30 from one binary and rows 31-58 from
# another, and the split was invisible in the TSV. Pass a pinned COPY of the
# binary, and this line is what proves you did.
printf '# binary %s sha256 %s\n' "$BIN" "$(sha256sum "$BIN" | cut -d' ' -f1)" > "$OUT"
printf '# policy %s\n' "${AXEYUM_UF_ARITH_OVERBOUND:-<default>}" >> "$OUT"
printf '# loadavg-at-start %s\n' "$(cut -d' ' -f1-3 /proc/loadavg)" >> "$OUT"
printf 'file\twall_ms\tverdict\troute_line\ttrail\n' >> "$OUT"

while IFS= read -r f; do
  [ -z "$f" ] && continue
  start=$(date +%s%N)
  raw=$(ulimit -v 8388608; timeout 40 "$BIN" --trace --timeout-ms 24000 "$f" 2>&1)
  end=$(date +%s%N)
  wall=$(( (end - start) / 1000000 ))
  verdict=$(printf '%s\n' "$raw" | grep -v '^;' | tail -1)
  route=$(printf '%s\n' "$raw" | grep '^; route ' | head -1)
  trail=$(printf '%s\n' "$raw" | grep '^; route-trail ' | head -1)
  printf '%s\t%s\t%s\t%s\t%s\n' "$f" "$wall" "$verdict" "$route" "$trail" >> "$OUT"
  printf 'done %s %sms %s\n' "$(basename "$f")" "$wall" "$verdict"
done < "$LIST"
echo "SWEEP_COMPLETE $OUT"
