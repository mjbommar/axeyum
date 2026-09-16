#!/usr/bin/env bash
# DT-ARRAY-ELEMENT -- the INTERLEAVED A/B: ONE binary, TWO env values, both
# arms of a file back to back on the SAME core.
#
#   ab-run.sh <list> <out.tsv> <pin> <bin> [budget_s]
#
# INTERLEAVED PER FILE, and that is the whole method. Load on these boxes moves
# these numbers more than most code changes do -- CLAUDE.md records one sweep
# reading 35 / 39 / 40 verdicts on a single commit purely from load -- and
# running arm A over the whole list and then arm B over the whole list measures
# the load difference between the two halves of the afternoon. Back to back on
# one core, the load cancels in the DIFFERENCE, which is the only quantity this
# file reports.
#
# ONE BINARY. The lever's OFF arm is `field_is_opaque` reduced to
# `matches!(sort, Sort::Datatype(_))`, the pre-ADR-2135 predicate verbatim, so
# the same executable is both arms and no build difference can be mistaken for
# a lever difference.
#
# ORDER IS ALTERNATED per file (base-first on even lines, arm-first on odd), so
# a systematic first-run penalty -- page cache, CPU boost state -- cannot land
# on one arm.
#
# THE ELAPSED COLUMN, AND WHY IT IS NOT `date +%s%3N`. That is what
# `bench-results/dt-field-expansion-20260916/ab-run.sh` uses, and on s7 -- where
# both lanes ran -- it is WRONG. s7 carries **uutils coreutils 0.8.0**, not GNU
# coreutils, and its `date` ignores the width modifier in `%3N`: it prints the
# full NINE nanosecond digits, so `%s%3N` is a 19-digit number and every
# difference taken from it is nanoseconds wearing a column header that says
# milliseconds. Measured 2026-09-16: `for i in $(seq 30); do date +%s%3N; done`
# gives 30 values of length **19** on s7, where GNU gives 13. Do not read a
# timing number out of any shard TSV written by the `date +%s%3N` form on this
# host -- this lane's first cost pass over its own captures reported a total
# elapsed of -20,454,778,950,164,076,537 ms, which is how it was found.
#
# `EPOCHREALTIME` is a bash builtin (bash 5.3 here), needs no external `date`,
# and is read under `LC_ALL=C` so its separator is a `.`. The self-check below
# runs BEFORE any solve and aborts if the clock is not plausibly a millisecond
# clock, so the column cannot quietly lie a second time.
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

export LC_ALL=C
now_ms() {  # epoch milliseconds, from the bash builtin -- no `date` involved
  local r=${EPOCHREALTIME/,/.}
  printf '%s%s' "${r%.*}" "$(printf '%.3s' "${r#*.}")"
}
# SELF-CHECK: a 200 ms sleep must read as 150-400 ms. A clock in nanoseconds
# reads ~200,000,000 and a stopped clock reads 0; both abort.
_t0=$(now_ms); sleep 0.2; _t1=$(now_ms); _d=$((_t1 - _t0))
if [ "$_d" -lt 150 ] || [ "$_d" -gt 400 ]; then
  echo "ABORT: now_ms() is not a millisecond clock (200 ms read as ${_d})"; exit 2
fi

printf 'file\tbase\tbase_ms\tarm\tarm_ms\tfirst\n' > "$OUT"
n=0
while IFS= read -r p; do
  [ -n "$p" ] || continue
  n=$((n + 1))
  run_base() {
    env -u AXEYUM_DT_ARRAY_ELEMENT taskset -c "$PIN" \
      timeout $((BUDGET + 40)) "$AX" "$p" --timeout-ms $((BUDGET * 1000)) 2>&1
  }
  run_arm() {
    env AXEYUM_DT_ARRAY_ELEMENT=on taskset -c "$PIN" \
      timeout $((BUDGET + 40)) "$AX" "$p" --timeout-ms $((BUDGET * 1000)) 2>&1
  }
  if [ $((n % 2)) -eq 0 ]; then
    first=base
    t0=$(now_ms); rb=$(run_base); t1=$(now_ms)
    t2=$(now_ms); ra=$(run_arm);  t3=$(now_ms)
  else
    first=arm
    t2=$(now_ms); ra=$(run_arm);  t3=$(now_ms)
    t0=$(now_ms); rb=$(run_base); t1=$(now_ms)
  fi
  vb=$(printf '%s\n' "$rb" | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
  va=$(printf '%s\n' "$ra" | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$(basename "$p")" "${vb:-NOVERDICT}" "$((t1 - t0))" \
    "${va:-NOVERDICT}" "$((t3 - t2))" "$first" >> "$OUT"
done < "$LIST"
echo "DONE $OUT"
