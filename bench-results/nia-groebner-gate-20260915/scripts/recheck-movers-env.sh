#!/usr/bin/env bash
# Re-run every MOVED row three times per arm, on ONE pinned core, at the same
# 24 s / 8 GiB envelope -- adapted from
# bench-results/route-ownership-20260915/recheck-movers.sh for ONE binary
# with two ENV settings (shipped vs the gate lever) instead of two binaries.
#
# Three passes per arm, and a row is classified only if all three agree:
#
#   STABLE-GAIN   shipped never decided, gate decided 3/3
#   STABLE-LOSS   shipped decided 3/3, gate never decided
#   UNSTABLE      anything else -- reported as ambient, not as an effect
#
# Usage: recheck-movers-env.sh <list> <out.tsv> <core> <bin> <lever_value> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; LEVER="$5"; BUDGET="${6:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }

one() {  # $1 = "shipped" | "gate"
  local raw rc v
  if [ "$1" = "shipped" ]; then
    raw=$(env -u AXEYUM_MAX_IDEAL_GENERATORS -u AXEYUM_MAX_IDEAL_ATOMS -u AXEYUM_MAX_IDEAL_INEQUALITIES \
            timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>/dev/null)
  else
    raw=$(env AXEYUM_MAX_IDEAL_GENERATORS="$LEVER" AXEYUM_MAX_IDEAL_ATOMS="$LEVER" AXEYUM_MAX_IDEAL_INEQUALITIES="$LEVER" \
            timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>/dev/null)
  fi
  rc=$?
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s/%s' "${v:-none}" "$rc"
}

printf 'file\tA1\tA2\tA3\tB1\tB2\tB3\tverdict\n' > "$OUT"
while read -r f; do
  [ -z "$f" ] && continue
  a1=$(one shipped); b1=$(one gate)
  b2=$(one gate); a2=$(one shipped)
  a3=$(one shipped); b3=$(one gate)

  av="${a1%%/*} ${a2%%/*} ${a3%%/*}"
  bv="${b1%%/*} ${b2%%/*} ${b3%%/*}"
  a_dec=$(printf '%s\n' $av | grep -cE '^(sat|unsat)$')
  b_dec=$(printf '%s\n' $bv | grep -cE '^(sat|unsat)$')
  if [ "$a_dec" -eq 0 ] && [ "$b_dec" -eq 3 ]; then cls=STABLE-GAIN
  elif [ "$a_dec" -eq 3 ] && [ "$b_dec" -eq 0 ]; then cls=STABLE-LOSS
  elif [ "$a_dec" -eq 3 ] && [ "$b_dec" -eq 3 ]; then cls=BOTH-DECIDE
  elif [ "$a_dec" -eq 0 ] && [ "$b_dec" -eq 0 ]; then cls=NEITHER-DECIDES
  else cls=UNSTABLE
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$a1" "$a2" "$a3" "$b1" "$b2" "$b3" "$cls" >> "$OUT"
  echo "$cls $f"
done < "$LIST"
echo "RECHECK-DONE -> $OUT"
