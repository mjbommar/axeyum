#!/usr/bin/env bash
# Per-division route-attribution sweep (ADR-1760).
#
# Extends the `bench-results/instrument-coverage-2026-09-07/scripts/
# run_division.sh` protocol with the ROUTE COLUMNS this lane added, so a normal
# parity run now records which route decided each file and which route consumed
# its budget:
#
#   division  file  wall_ms  verdict  decided_by  bound_by  last  bound_ms
#   trace_total_ms  attempts  log_path
#
# `decided_by` / `bound_by` / `last` come from the `; route …` line
# `smtcomp_cli --trace` prints (see `route_attribution_report_lines`). They are
# THREE columns and not one on purpose: classifying a file by the route that
# spoke last was refuted on 67 of 70 files in two divisions, so a consumer must
# never have to infer the binding route from the last one.
#
# The full ordered trail (`; route-trail <json>`) stays in the per-file log
# rather than the TSV -- it is a JSON object with one entry per dispatch
# attempt and does not belong in a tab-separated column.
#
# Selection is the deterministic first `min(N, total)` lines of the committed
# parity list, which unlike the loss-census lists carries files we WIN as well
# as files we lose. That is required here: the virtual-best-over-our-own-routes
# question is about the deciding-route distribution, and a loss-only population
# has no deciding routes to distribute.
set -uo pipefail

DIV="$1"
LIST="$2"
BIN="$3"
OUT_TSV="$4"
LOG_DIR="$5"
N="${6:-100}"
BUDGET_S="${7:-10}"

MEM_GB=8

mkdir -p "$LOG_DIR"

total=$(wc -l < "$LIST")
sample_n=$(( total < N ? total : N ))

echo "== $DIV: sampling first $sample_n of $total files (budget ${BUDGET_S}s) ==" >&2
printf 'division\tfile\twall_ms\tverdict\tdecided_by\tbound_by\tlast\tbound_ms\ttrace_total_ms\tattempts\tlog_path\n' > "$OUT_TSV"

idx=0
head -n "$sample_n" "$LIST" | while IFS= read -r file; do
  idx=$((idx + 1))
  [ -z "$file" ] && continue
  log_path="$LOG_DIR/${DIV}.${idx}.log"
  start_ns=$(date +%s%N)
  timeout -k 5 $(( BUDGET_S * 2 + 20 )) env AXEYUM_TRACE=1 bash -c '
    ulimit -v $(( '"$MEM_GB"' * 1024 * 1024 ))
    exec "$@"
  ' _ "$BIN" "$file" --timeout-ms "$((BUDGET_S * 1000))" > "$log_path" 2>&1
  end_ns=$(date +%s%N)
  wall_ms=$(( (end_ns - start_ns) / 1000000 ))

  verdict=$(grep -oE '^(sat|unsat)$' "$log_path" | tail -1)
  verdict="${verdict:-unsolved}"

  # One `; route …` line per run. Field-extract rather than positional-cut so a
  # future added field cannot silently shift a column.
  route_line=$(grep -m1 '^; route ' "$log_path")
  field() { printf '%s\n' "$route_line" | tr ' ' '\n' | sed -n "s/^$1=//p" | head -1; }
  decided_by=$(field decided_by); decided_by="${decided_by:-NA}"
  bound_by=$(field bound_by);     bound_by="${bound_by:-NA}"
  last=$(field last);             last="${last:-NA}"
  bound_ms=$(field bound_ms);     bound_ms="${bound_ms:-NA}"
  trace_ms=$(field total_ms);     trace_ms="${trace_ms:-NA}"
  attempts=$(field attempts);     attempts="${attempts:-NA}"

  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$DIV" "$file" "$wall_ms" "$verdict" \
    "$decided_by" "$bound_by" "$last" "$bound_ms" "$trace_ms" "$attempts" \
    "$log_path" >> "$OUT_TSV"
done

echo "== $DIV done ==" >&2
