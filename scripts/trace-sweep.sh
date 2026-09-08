#!/usr/bin/env bash
# Run one file list through `smtcomp_cli --trace`, serially, keeping the whole
# stdout per file, so `scripts/trace-sweep-report.py` can say where each file's
# budget went.
#
#   scripts/cargo-serialized.sh build --release -p axeyum-bench --example smtcomp_cli
#   scripts/trace-sweep.sh <file-list> <out-dir> [budget_s=24]
#   scripts/trace-sweep-report.py <out-dir> "<label>"
#
# `<out-dir>/index.tsv` is `index, file, verdict, wall_ms`; `<out-dir>/<n>.log`
# is that file's whole trace block. Written 2026-09-08 for the population the
# cross-thread instrument board was built for — 22 `QF_LRA` files that print no
# `; theory-layer` line and the 27 `QF_LIA` losses — and kept because the answer
# (`bench-results/watchdog-blind-files-20260908/`) is only worth as much as the
# ability to take it again.
#
# Serial, never parallel: the numbers read out of these logs are stage timings,
# and the frontier-ratchet reference-frame note measures the same sweep at
# 35/39/40 on one machine at three load levels. `taskset -c 0-7` for the same
# reason — this is a hybrid CPU and an unpinned run is 1.84x slower on the
# E-cores.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT" || exit 1

LIST="$1"
OUT="$2"
BUDGET_S="${3:-24}"
BIN="$ROOT/target/release/examples/smtcomp_cli"

mkdir -p "$OUT"
: >"$OUT/index.tsv"
printf 'index\tfile\tverdict\twall_ms\n' >>"$OUT/index.tsv"

n=0
while IFS= read -r file; do
  [ -z "$file" ] && continue
  n=$((n + 1))
  log="$OUT/$n.log"
  start=$(date +%s%N)
  ( ulimit -v $((8 * 1024 * 1024)); \
    taskset -c 0-7 timeout "$((BUDGET_S + 6))" "$BIN" "$file" \
      --timeout-ms "$((BUDGET_S * 1000))" --trace ) >"$log" 2>&1
  end=$(date +%s%N)
  wall=$(( (end - start) / 1000000 ))
  verdict=$(grep -m1 -E '^(sat|unsat|unknown)$' "$log")
  printf '%s\t%s\t%s\t%s\n' "$n" "$file" "${verdict:-ABORTED}" "$wall" >>"$OUT/index.tsv"
  echo "[$n] ${verdict:-ABORTED} ${wall}ms $(basename "$file")"
done <"$LIST"
echo "done: $n files -> $OUT"
