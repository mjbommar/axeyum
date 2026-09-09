#!/usr/bin/env bash
# Re-cut sweep: one axeyum run per file, byte-identical to the SCORED path of
# `scripts/parity-run.sh` (the recipe every committed parity number was measured
# with), so a verdict here is comparable to the 2026-09-05 census's.
#
#   MEM_LIMIT_GB=8 timeout $((b+5)) env -u AXEYUM_EVIDENCE \
#     scripts/mem-run.sh <bin> <file> --timeout-ms $((b*1000)) \
#     | grep -oE '^(sat|unsat)$' | tail -1
#
# The external `timeout` is b+5, exactly as in parity-run.sh: this sweep must
# reproduce the SHIPPED scoring, watchdog grace included, not a stricter one.
# Whether a file needed that grace is a separate column (`over_budget`), not a
# different verdict -- conflating the two would silently redefine the metric in
# the middle of a re-measurement whose whole point is comparability.
#
# Usage: sweep.sh <list-file> <division> <out-tsv>
set -uo pipefail
list="$1"
division="$2"
out="$3"
root="$(cd "$(dirname "$0")/../../.." && pwd)"
bin="$root/target/release/examples/smtcomp_cli"
b="${PARITY_BUDGET_S:-24}"
mem="${PARITY_MEM_GB:-8}"

if [ ! -x "$bin" ]; then
  echo "sweep.sh: missing $bin -- cargo build --release -p axeyum-bench --example smtcomp_cli" >&2
  exit 2
fi

printf 'file\tdivision\tverdict\twall_ms\tdeclared\tover_budget\n' > "$out"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  declared=$(grep -m1 ':status' "$f" 2>/dev/null | grep -oE '\b(unsat|sat|unknown)\b' | head -1)
  # %s%N (nanoseconds), NOT %s%3N: measured on this fleet 2026-09-08, `date`
  # here ignores the width and returns the full 9 digits, which turned a 24 s
  # run into a "24233199579 ms" cell in the first smoke run.
  t0=$(date +%s%N)
  verdict=$(MEM_LIMIT_GB="$mem" timeout "$((b + 5))" \
            env -u AXEYUM_EVIDENCE "$root/scripts/mem-run.sh" \
            "$bin" "$f" --timeout-ms "$((b * 1000))" 2>/dev/null \
            | grep -oE '^(sat|unsat)$' | tail -1)
  t1=$(date +%s%N)
  ms=$(( (t1 - t0) / 1000000 ))
  over=no
  if [ "$ms" -gt "$((b * 1000))" ]; then over=yes; fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$f" "$division" "${verdict:-unsolved}" "$ms" "${declared:-none}" "$over" >> "$out"
done < "$list"
