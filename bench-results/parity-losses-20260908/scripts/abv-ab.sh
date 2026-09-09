#!/usr/bin/env bash
# Per-file A/B of the `abv-online-cdclt` ladder reserve on the files the
# portfolio lane named as "wins we keep only by overrunning the budget".
#
# Reads the `; route ... bound_ms=... total_ms=...` trailer, so the finding is
# not "the file is still sat" (it was sat before too, by grace) but "the file is
# decided INSIDE the budget it was given". Those are different claims and only
# the second one survives a hard external limit.
#
# Usage: abv-ab.sh <list> <arm: on|off> <out-tsv>
set -uo pipefail
list="$1"; arm="$2"; out="$3"
root="$(cd "$(dirname "$0")/../../.." && pwd)"
bin="$root/target/release/examples/smtcomp_cli"
b="${PARITY_BUDGET_S:-24}"
mem="${PARITY_MEM_GB:-8}"

# Pin the solve, not the harness, so the two arms share a core class. The host
# carries other lanes; `AB_CORES` keeps this measurement off the cores the
# re-cut sweep is using rather than pretending the box is idle.
pin=()
if [ -n "${AB_CORES:-}" ]; then pin=(taskset -c "$AB_CORES"); fi

printf 'file\tarm\tverdict\twall_ms\tbound_by\tbound_ms\ttotal_ms\tdecided_by\n' > "$out"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  t0=$(date +%s%N)
  raw=$(MEM_LIMIT_GB="$mem" timeout "$((b + 5))" \
        env -u AXEYUM_EVIDENCE AXEYUM_ABV_ONLINE_RESERVE="$arm" \
        "${pin[@]}" "$root/scripts/mem-run.sh" "$bin" "$f" --timeout-ms "$((b * 1000))" --trace 2>/dev/null)
  t1=$(date +%s%N)
  ms=$(( (t1 - t0) / 1000000 ))
  verdict=$(printf '%s\n' "$raw" | grep -oE '^(sat|unsat)$' | tail -1)
  route=$(printf '%s\n' "$raw" | grep -m1 '^; route ')
  bound_by=$(printf '%s\n' "$route" | grep -oE 'bound_by=[^ ]+' | cut -d= -f2)
  bound_ms=$(printf '%s\n' "$route" | grep -oE 'bound_ms=[0-9]+' | cut -d= -f2)
  total_ms=$(printf '%s\n' "$route" | grep -oE 'total_ms=[0-9]+' | cut -d= -f2)
  decided_by=$(printf '%s\n' "$route" | grep -oE 'decided_by=[^ ]+' | cut -d= -f2)
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$f" "$arm" "${verdict:-unsolved}" "$ms" "${bound_by:-none}" \
    "${bound_ms:-none}" "${total_ms:-none}" "${decided_by:-none}" >> "$out"
done < "$list"
