#!/usr/bin/env bash
# Re-run every MOVED row three times per arm, on ONE pinned core, at the same
# 24 s / 8 GiB envelope.
#
# WHY. A single interleaved pairing at 24 s carries a measured 1-1.5 % ambient
# flip rate on these boxes. ADR-1966 reported 25 raw movers and 22 after
# re-checking: **11 of its 18 movers outside the treatment division vanished**,
# and reporting the raw column would have overstated the effect by 11 files and
# the cost by 5. ADR-1980 re-ran all 83 of its movers and found 81 STABLE-GAIN,
# 2 STABLE-LOSS, 0 UNSTABLE.
#
# Three passes per arm, and a row is classified only if all three agree:
#
#   STABLE-GAIN   A never decided, B decided 3/3
#   STABLE-LOSS   A decided 3/3, B never decided
#   UNSTABLE      anything else -- reported as ambient, not as an effect
#
# EXIT STATUS is recorded per pass as its own column: ADR-2045 measured
# `losses=0` by verdict and five new ABORTS underneath it.
#
# Usage: recheck-movers.sh <list> <out.tsv> <cores> <binA> <binB> [budget_s]
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

one() {  # $1 = binary
  local raw rc v
  raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
          "$1" "$f" 2>/dev/null)
  rc=$?
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s/%s' "${v:-none}" "$rc"
}

printf 'file\tA1\tA2\tA3\tB1\tB2\tB3\tverdict\n' > "$OUT"
while read -r f; do
  [ -z "$f" ] && continue
  # Arms alternate WITHIN the three passes too, so a drift in machine state
  # across the ~2.5 minutes a row takes does not land entirely on one arm.
  a1=$(one "$AX_A"); b1=$(one "$AX_B")
  b2=$(one "$AX_B"); a2=$(one "$AX_A")
  a3=$(one "$AX_A"); b3=$(one "$AX_B")

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
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "${f#"$CORPUS"}" "$a1" "$a2" "$a3" "$b1" "$b2" "$b3" "$cls" >> "$OUT"
  echo "$cls ${f#"$CORPUS"}"
done < "$LIST"
echo "RECHECK-DONE -> $OUT"
