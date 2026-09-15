#!/usr/bin/env bash
# DT-QUANT-TRACE -- run OUR solver over a list with the route trail on, and
# record the decline wording verbatim.
#
#   ax-trace.sh <list> <out.tsv> <pin> <bin> [budget_s] [extra env assignments...]
#
# `AXEYUM_QPROBE=1` is ON. It is the only channel that separates "the MBQI
# refutation loop ran and its GROUND seed solve refused" from "a shape guard
# fired and the call was e-matching all along": both are the same
# `Ok(Unknown)` at the call site (`auto.rs`'s `mbqi_shape_probe` doc comment
# says so in those words), and they are completely different findings. The
# census in this lane turns on exactly that distinction, so it is measured
# rather than read off the message.
#
# The give-up detail is carried VERBATIM and unbucketed. Sizing a bucket by its
# LABEL is how ADR-2020's census reported one cause where the raw details held
# four -- and in this lane the label is actively misleading, because
# `relabel_with_datatype_refusal` (auto.rs:7911) puts the DATATYPE rung's
# sentence in front of a refusal the datatype rung did not produce.
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
shift 5 || true
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

printf 'file\tverdict\tbound_by\tlast\tattempts\ttotal_ms\tgiveup_kind\tmbqi_exit\tmbqi_census\tgiveup_raw\n' > "$OUT"
while IFS= read -r p; do
  [ -n "$p" ] || continue
  raw=$(env AXEYUM_TRACE=1 AXEYUM_QPROBE=1 "$@" \
          taskset -c "$PIN" timeout $((BUDGET + 40)) \
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
  # EVERY mbqi-shape exit, joined with `,`: the loop is re-entered per rung and
  # a single `head -1` would report the first entry as if it were the only one.
  mx=$(printf '%s\n' "$raw" | sed -n 's/.*\[mbqi-shape\] exit=\([a-z-]*\).*/\1/p' \
        | paste -sd, - )
  mc=$(printf '%s\n' "$raw" | grep -m1 '\[mbqi-census\]' | sed 's/.*\[mbqi-census\] //')
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$(basename "$p")" "${v:-NOVERDICT}" "${bb:-NONE}" "${lb:-NONE}" \
    "${at:-0}" "${ms:-0}" "${gk:-NONE}" "${mx:-NONE}" "${mc:-NONE}" "${gd:-NONE}" >> "$OUT"
done < "$LIST"
echo "DONE $OUT"
