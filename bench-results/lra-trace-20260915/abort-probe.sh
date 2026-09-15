#!/usr/bin/env bash
# LRA-TRACE: do the 40 `rc=134` rows still abort under the sparse tableau?
#
# This is a MECHANISM probe, not the A/B, and it is labelled as one in its own
# output (`ADVISORY`).  It asks one binary question per file -- does the process
# die in an allocation -- and reports the exit status and the peak resident set,
# not a verdict count.  A verdict delta measured this way would be the 77/79/85
# error: the arms are run back to back on whatever core the caller pinned, and
# nothing here calibrates the machine.
#
# Why it is worth taking anyway: an abort is a bug class rather than a capacity
# limit, and "did the abort stop" is answerable without a comparable timing
# frame.  [ADR-2045] measured that converting these rows to clean `unknown`s
# decides NOTHING, so the verdict question is already known to need the full
# interleaved A/B to answer, and this probe deliberately does not pretend to.
#
# Arms run A, B, B, A per file so a drift across the pair does not land on one.
#
# Usage: abort-probe.sh <list> <out.tsv> <cores> <binA> <binB> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX_A="$4"; AX_B="$5"; BUDGET="${6:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX_A" ] || { echo "ABORT: $AX_A missing"; exit 2; }
[ -x "$AX_B" ] || { echo "ABORT: $AX_B missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }
HA=$(sha256sum "$AX_A" | cut -d' ' -f1)
HB=$(sha256sum "$AX_B" | cut -d' ' -f1)
[ "$HA" = "$HB" ] && { echo "ABORT: both arms are the SAME binary"; exit 2; }

one() {  # $1 = binary; prints "<verdict>/<rc>/<peak_kb>"
  local raw rc v peak
  peak=$( { /usr/bin/time -f '%M' timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$1" "$f" > /tmp/lra-trace-probe.$$.out 2>/dev/null; echo "RC=$?" >&2; } 2>&1 )
  rc=$(printf '%s\n' "$peak" | grep -oE 'RC=[0-9]+' | head -1 | cut -d= -f2)
  peak=$(printf '%s\n' "$peak" | grep -vE 'RC=' | tail -1)
  v=$(grep -m1 -oE '^(sat|unsat|unknown)$' -- /tmp/lra-trace-probe.$$.out 2>/dev/null || true)
  rm -f /tmp/lra-trace-probe.$$.out
  printf '%s/%s/%s' "${v:-none}" "${rc:-?}" "${peak:-?}"
}

printf 'file\tA1\tB1\tB2\tA2\n' > "$OUT"
while read -r rel; do
  [ -z "$rel" ] && continue
  f="$CORPUS$rel"
  [ -r "$f" ] || { echo "UNREADABLE $rel" >&2; continue; }
  a1=$(one "$AX_A"); b1=$(one "$AX_B"); b2=$(one "$AX_B"); a2=$(one "$AX_A")
  printf '%s\t%s\t%s\t%s\t%s\n' "$rel" "$a1" "$b1" "$b2" "$a2" >> "$OUT"
done < "$LIST"

echo "ADVISORY: mechanism probe (abort / peak RSS). NOT a verdict measurement."
echo "PROBE-DONE $(($(wc -l < "$OUT") - 1)) rows"
