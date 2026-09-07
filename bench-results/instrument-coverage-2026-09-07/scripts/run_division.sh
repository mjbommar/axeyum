#!/usr/bin/env bash
# Re-run of the bench-divisions 2026-09-07 per-division timing sample, now with
# every instrument this lane added (`; front-door …`, `; dl-online …`,
# `; bv-layer …`) alongside the pre-existing `; theory-layer …` line, all under
# the same `--trace`/`AXEYUM_TRACE=1` flag. Same selection rule, same protocol
# as the original `bench-results/bench-divisions-2026-09-07/scripts/
# run_division.sh` (deterministic first `min(8, N)` lines of the committed
# 2026-09-05/06 loss-census list, 24s wall / 8GiB ulimit -v).
#
# Differs from the original script in ONE way: it captures the FULL stdout
# per file to a log (a query can now print more than one `; …` line, so a
# single `grep -m1 '^; theory-layer'` column can no longer hold everything),
# and the TSV records the log path instead of one trace_line column.
set -uo pipefail

DIV="$1"
LIST="$2"
BIN="$3"
OUT_TSV="$4"
LOG_DIR="$5"
N="${6:-8}"

MEM_GB=8
BUDGET_S=24

mkdir -p "$LOG_DIR"

total=$(wc -l < "$LIST")
sample_n=$(( total < N ? total : N ))

echo "== $DIV: sampling first $sample_n of $total lost files ==" >&2
echo -e "division\tfile\twall_ms\tverdict\tlog_path" > "$OUT_TSV"

idx=0
head -n "$sample_n" "$LIST" | while IFS= read -r file; do
  idx=$((idx + 1))
  log_path="$LOG_DIR/${DIV}.${idx}.log"
  start_ns=$(date +%s%N)
  timeout -k 5 45 env AXEYUM_TRACE=1 bash -c '
    ulimit -v $(( '"$MEM_GB"' * 1024 * 1024 ))
    exec "$@"
  ' _ "$BIN" "$file" --timeout-ms "$((BUDGET_S * 1000))" > "$log_path" 2>&1
  end_ns=$(date +%s%N)
  wall_ms=$(( (end_ns - start_ns) / 1000000 ))
  verdict=$(grep -oE '^(sat|unsat)$' "$log_path" | tail -1)
  verdict="${verdict:-unsolved}"
  printf '%s\t%s\t%s\t%s\t%s\n' "$DIV" "$file" "$wall_ms" "$verdict" "$log_path" >> "$OUT_TSV"
  echo "  $file -> ${verdict} (${wall_ms} ms)" >&2
done

echo "== $DIV done ==" >&2
