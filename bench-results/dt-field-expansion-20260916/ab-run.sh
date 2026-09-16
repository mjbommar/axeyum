#!/usr/bin/env bash
# DT-FIELD-EXPANSION -- the INTERLEAVED A/B: ONE binary, TWO env values, both
# arms of a file back to back on the SAME core.
#
#   ab-run.sh <list> <out.tsv> <pin> <bin> [budget_s] [depth]
#
# INTERLEAVED PER FILE, and that is the whole method. Load on this box moves
# these numbers more than most code changes do -- CLAUDE.md records one sweep
# reading 35 / 39 / 40 verdicts on a single commit purely from load -- and
# running arm A over the whole list and then arm B over the whole list measures
# the load difference between the two halves of the afternoon. Back to back on
# one core, the load cancels in the DIFFERENCE, which is the only quantity this
# file reports.
#
# ONE BINARY. The lever's OFF arm is `datatype_expansion_is_exact_to_depth(dt, 0)`,
# which is the pre-ADR-2128 predicate verbatim, so the same executable is both
# arms and no build difference can be mistaken for a lever difference.
#
# ORDER IS ALTERNATED per file (base-first on even lines, arm-first on odd), so
# a systematic first-run penalty -- page cache, CPU boost state -- cannot land
# on one arm.
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"; DEPTH="${6:-5}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

printf 'file\tbase\tbase_ms\tarm\tarm_ms\tfirst\n' > "$OUT"
n=0
while IFS= read -r p; do
  [ -n "$p" ] || continue
  n=$((n + 1))
  run_base() {
    env -u AXEYUM_DT_NESTED_FIELD_DEPTH taskset -c "$PIN" \
      timeout $((BUDGET + 40)) "$AX" "$p" --timeout-ms $((BUDGET * 1000)) 2>&1
  }
  run_arm() {
    env AXEYUM_DT_NESTED_FIELD_DEPTH="$DEPTH" taskset -c "$PIN" \
      timeout $((BUDGET + 40)) "$AX" "$p" --timeout-ms $((BUDGET * 1000)) 2>&1
  }
  if [ $((n % 2)) -eq 0 ]; then
    first=base
    t0=$(date +%s%3N); rb=$(run_base); t1=$(date +%s%3N)
    t2=$(date +%s%3N); ra=$(run_arm);  t3=$(date +%s%3N)
  else
    first=arm
    t2=$(date +%s%3N); ra=$(run_arm);  t3=$(date +%s%3N)
    t0=$(date +%s%3N); rb=$(run_base); t1=$(date +%s%3N)
  fi
  vb=$(printf '%s\n' "$rb" | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
  va=$(printf '%s\n' "$ra" | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$(basename "$p")" "${vb:-NOVERDICT}" "$((t1 - t0))" \
    "${va:-NOVERDICT}" "$((t3 - t2))" "$first" >> "$OUT"
done < "$LIST"
echo "DONE $OUT"
