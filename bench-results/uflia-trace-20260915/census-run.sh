#!/usr/bin/env bash
# UFLIA-TRACE -- traced census over one list of .smt2 paths.
#
#   census-run.sh <list> <out.tsv> <pin> <bin> [budget_s]
#
# Emits, per file: the terminal typed route reason (`bound_by`/`last`), the
# give-up kind and its VERBATIM detail (sizing a bucket by its LABEL is how a
# census reports one cause where the raw details hold four), plus the
# e-matching shape the give-up text alone cannot carry:
#
#   universals   distinct CompiledUniversals in the widest matcher build
#   triggerless  of those, compiled with `patterns=0`
#   rounds       fixpoint rounds entered
#   joined       trigger joins found across all rounds
#   admitted     instances actually admitted across all rounds
#   silent       universals whose `admitted` is 0 in EVERY round they appear
#
# `AXEYUM_QPROBE=1` is extra work inside the binary, so this pass never doubles
# as a verdict measurement: the verdict column here exists only to be compared
# against the untraced arm, not to be quoted.
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
HERE="$(cd "$(dirname "$0")" && pwd)"

printf 'file\tverdict\tbound_by\tlast\tattempts\ttotal_ms\tgiveup_kind\tuniversals\ttriggerless\trounds\tjoined\tstarved\tadmitted\tsilent\tgiveup_raw\n' > "$OUT"
while IFS= read -r p; do
  [ -n "$p" ] || continue
  raw=$(AXEYUM_TRACE=1 AXEYUM_QPROBE=1 taskset -c "$PIN" timeout $((BUDGET + 40)) \
          "$AX" "$p" --timeout-ms $((BUDGET * 1000)) 2>&1)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
  rl=$(printf '%s\n' "$raw" | grep -m1 '^; route ' || true)
  bb=$(printf '%s' "$rl" | grep -oE 'bound_by=[^ ]+' | cut -d= -f2)
  lb=$(printf '%s' "$rl" | grep -oE ' last=[^ ]+' | cut -d= -f2)
  at=$(printf '%s' "$rl" | grep -oE 'attempts=[0-9]+' | cut -d= -f2)
  ms=$(printf '%s' "$rl" | grep -oE 'total_ms=[0-9]+' | cut -d= -f2)
  gl=$(printf '%s\n' "$raw" | grep -m1 '^; give-up ' || true)
  gk=$(printf '%s' "$gl" | grep -oE 'kind=[A-Za-z]+' | cut -d= -f2)
  gd=$(printf '%s' "$gl" | sed -n 's/.*detail=//p' | tr '\t\n' '  ')
  shape=$(printf '%s\n' "$raw" | python3 "$HERE/probe-shape.py")
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$(basename "$p")" "${v:-NOVERDICT}" "${bb:-NONE}" "${lb:-NONE}" \
    "${at:-0}" "${ms:-0}" "${gk:-NONE}" "$shape" "${gd:-NONE}" >> "$OUT"
done < "$LIST"
echo "DONE $OUT"
