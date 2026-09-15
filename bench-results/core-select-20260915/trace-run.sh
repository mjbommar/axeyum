#!/usr/bin/env bash
# CORE-SELECT -- WHY we fail on a subset, for the rows where the ceiling is
# negative (we are `unknown` even on the reference's own minimal core).
#
#   trace-run.sh <list-of-subset-files> <out.tsv> <pin> <bin> [budget_s]
#
# Deliberately a SEPARATE pass from `sim-run.sh`. `AXEYUM_TRACE=1` is extra work
# inside the binary, so folding it into the verdict measurement would make the
# R6 ceiling a measurement of a traced build. The ceiling is measured untraced;
# this pass only explains rows the ceiling has already classified.
#
# `bound_by` NONE with `attempts=1` whose only entry is the unconditional
# `fd:parse` probe is the RUNG-NEVER-REACHED shape; `attempts` is carried so a
# census cannot rank blockers off a ladder that refused at its first rung.
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

printf 'subset\tverdict\tbound_by\tlast\tattempts\ttotal_ms\tgiveup_kind\tgiveup_raw\n' > "$OUT"
while IFS= read -r p; do
  [ -n "$p" ] || continue
  raw=$(AXEYUM_TRACE=1 taskset -c "$PIN" timeout $((BUDGET + 40)) \
          "$AX" "$p" --timeout-ms $((BUDGET * 1000)) 2>&1)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
  rl=$(printf '%s\n' "$raw" | grep -m1 '^; route ' || true)
  bb=$(printf '%s' "$rl" | grep -oE 'bound_by=[^ ]+' | cut -d= -f2)
  lb=$(printf '%s' "$rl" | grep -oE ' last=[^ ]+' | cut -d= -f2)
  at=$(printf '%s' "$rl" | grep -oE 'attempts=[0-9]+' | cut -d= -f2)
  ms=$(printf '%s' "$rl" | grep -oE 'total_ms=[0-9]+' | cut -d= -f2)
  gl=$(printf '%s\n' "$raw" | grep -m1 '^; give-up ' || true)
  gk=$(printf '%s' "$gl" | grep -oE 'kind=[A-Za-z]+' | cut -d= -f2)
  # VERBATIM and unbucketed: sizing a bucket by its LABEL is how a census
  # reports one cause where the raw details hold four.
  gd=$(printf '%s' "$gl" | sed -n 's/.*detail=//p' | tr '\t\n' '  ')
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$(basename "$p")" "${v:-NOVERDICT}" "${bb:-NONE}" "${lb:-NONE}" \
    "${at:-0}" "${ms:-0}" "${gk:-NONE}" "${gd:-NONE}" >> "$OUT"
done < "$LIST"
echo "DONE $OUT"
