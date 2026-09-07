#!/usr/bin/env bash
# Runs the bench-divisions timing sample for one division against the current
# smtcomp_cli release binary. Deterministic selection: the first N lines
# (N = min(8, file count)) of the committed 2026-09-05/06 loss-census list for
# that division (bench-results/parity-losses-<date>/<DIV>.txt), in file order.
# AXEYUM_TRACE=1, 24s/8GiB protocol identical to scripts/parity-run.sh.
set -uo pipefail

DIV="$1"
LIST="$2"
BIN="$3"
OUT_TSV="$4"
N="${5:-8}"

MEM_GB=8
BUDGET_S=24

total=$(wc -l < "$LIST")
sample_n=$(( total < N ? total : N ))

echo "== $DIV: sampling first $sample_n of $total lost files ==" >&2
echo -e "division\tfile\twall_ms\tverdict\ttrace_line" > "$OUT_TSV"

head -n "$sample_n" "$LIST" | while IFS= read -r file; do
  start_ns=$(date +%s%N)
  out=$(timeout -k 5 45 env AXEYUM_TRACE=1 bash -c '
    ulimit -v $(( '"$MEM_GB"' * 1024 * 1024 ))
    exec "$@"
  ' _ "$BIN" "$file" --timeout-ms "$((BUDGET_S * 1000))" 2>&1)
  end_ns=$(date +%s%N)
  wall_ms=$(( (end_ns - start_ns) / 1000000 ))
  verdict=$(printf '%s\n' "$out" | grep -oE '^(sat|unsat)$' | tail -1)
  verdict="${verdict:-unsolved}"
  trace_line=$(printf '%s\n' "$out" | grep -m1 '^; theory-layer' || true)
  printf '%s\t%s\t%s\t%s\t%s\n' "$DIV" "$file" "$wall_ms" "$verdict" "$trace_line" >> "$OUT_TSV"
  echo "  $file -> ${verdict} (${wall_ms} ms)" >&2
done

echo "== $DIV done ==" >&2
