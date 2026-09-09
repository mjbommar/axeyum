#!/usr/bin/env bash
# Lane uflia-after-reachability: run a list through smtcomp_cli --trace and keep
# the FULL `;` instrumentation output per file, not only the route line.
#
# Usage: sweep.sh <list.txt> <binary> <outdir> [policy]
# Protocol: 24 s wall, 8 GiB `ulimit -v`, one file at a time — the same numbers
# scripts/parity-run.sh uses, so results are comparable to the ledger.
set -uo pipefail

LIST="$1"; BIN="$2"; OUTDIR="$3"
if [ "$#" -ge 4 ]; then export AXEYUM_UF_ARITH_OVERBOUND="$4"; fi
mkdir -p "$OUTDIR/raw"
OUT="$OUTDIR/summary.tsv"

# The binary digest goes in FIRST: a sweep that reads target/release/... while a
# build is writing it silently changes solver mid-run, and nothing in the TSV
# says so. Pass a pinned COPY and this line is what proves you did.
printf '# binary %s sha256 %s\n' "$BIN" "$(sha256sum "$BIN" | cut -d' ' -f1)" > "$OUT"
printf '# policy %s\n' "${AXEYUM_UF_ARITH_OVERBOUND:-<default>}" >> "$OUT"
printf '# host %s loadavg-at-start %s\n' "$(hostname)" "$(cut -d' ' -f1-3 /proc/loadavg)" >> "$OUT"
printf 'file\twall_ms\tverdict\n' >> "$OUT"

i=0
while IFS= read -r f; do
  [ -z "$f" ] && continue
  i=$((i+1))
  key=$(printf '%s' "$f" | sha256sum | cut -c1-12)
  start=$(date +%s%N)
  raw=$( (ulimit -v 8388608; timeout 45 "$BIN" --trace --timeout-ms 24000 "$f") 2>&1 )
  end=$(date +%s%N)
  wall=$(( (end - start) / 1000000 ))
  printf '%s\n' "$raw" > "$OUTDIR/raw/$key.txt"
  printf '# lane-file %s\n' "$f" >> "$OUTDIR/raw/$key.txt"
  verdict=$(printf '%s\n' "$raw" | grep -v '^;' | grep -E '^(sat|unsat|unknown)$' | tail -1)
  [ -z "$verdict" ] && verdict="none"
  printf '%s\t%s\t%s\n' "$f" "$wall" "$verdict" >> "$OUT"
  printf 'done %d %s %sms %s\n' "$i" "$(basename "$f")" "$wall" "$verdict"
done < "$LIST"
echo "SWEEP_COMPLETE $OUT"
