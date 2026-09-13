#!/usr/bin/env bash
# Does the `uf-nra` rung's guard fire on the ONLY division that can enter it?
#
# The first firing scan covered NRA / QF_NRA / AUFNIRA / UFNIA and found zero.
# That was a VACUOUS negative: `dispatch_uf_nra`'s own gate requires
# `has_real && has_function && !has_int && !has_array && !has_datatype &&
# !has_uninterpreted_sort`, which NRA and QF_NRA (no UF) and AUFNIRA (arrays)
# and UFNIA (ints) all fail by construction. `QF_UFNRA` is the division whose
# logic matches the gate. All 58 of its files, not a sample.
set -u
AX=/data0/axeyum/dispatch-decline-audit-bin/fix
LIST=/data0/axeyum/dispatch-decline-audit-bin/QF_UFNRA-all.txt
OUT=/data0/axeyum/dispatch-decline-audit-guards/QF_UFNRA.trails
VLIM=$((8 * 1024 * 1024))
: > "$OUT"
while read -r f; do
  [ -n "$f" ] || continue
  timeout 14 taskset -c 13 \
    bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms 10000" \
    "$AX" "$f" 2>/dev/null | grep -m1 'route-trail' >> "$OUT"
done < "$LIST"
echo "QF_UFNRA trails=$(wc -l < "$OUT")"
echo "uf-nra entered: $(grep -c '"route":"uf-nra"' "$OUT")"
echo "uf-nra unsupported-decline: $(grep -c '"route":"uf-nra","outcome":"declined","reason":"unsupported"' "$OUT")"
