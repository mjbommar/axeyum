#!/usr/bin/env bash
# QUANT-ACTIVATION -- re-run every MOVED row three times per arm, on ONE pinned
# core, at the same 24 s / 8 GiB envelope.
#
# This is `bench-results/route-ownership-20260915/recheck-movers.sh` adapted to a
# ONE-BINARY, TWO-ENV-VALUE A/B. Its same-binary abort does not apply here and is
# replaced by the failure it was guarding against in the shape this A/B can have
# it: if the variable never reaches the solve, BOTH arms are the shipped arm and
# every mover comes back UNSTABLE, which reads like ambient noise. So the
# `ab-self-check.sh` VERDICT check is re-run first and this refuses on its exit
# status.
#
# WHY RE-CHECK AT ALL. A single interleaved pairing at 24 s carries a measured
# 1-1.5 % ambient flip rate on these boxes. ADR-1966 reported 25 raw movers and
# 22 after re-checking -- 11 of its 18 out-of-division movers vanished -- and
# reporting the raw column would have overstated the effect by 11 files.
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
# Usage: recheck-movers.sh <list> <out.tsv> <cores> <bin> <valueB> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; VB="$5"; BUDGET="${6:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/
HERE="$(cd "$(dirname "$0")" && pwd)"

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }
case "$VB" in
  ''|0) echo "ABORT: arm B value '$VB' is the shipped arm; both arms would be A"; exit 2 ;;
esac
bash "$HERE/ab-self-check.sh" "$AX" "$VB" || {
  echo "ABORT: the self-check failed, so an UNSTABLE column here would be a"
  echo "  variable that never arrived rather than ambient noise"
  exit 3
}

one() {  # $1 = "" for the shipped arm, else the level value
  local raw rc v
  if [ -z "$1" ]; then
    raw=$(env -u AXEYUM_QINST_POSITIVE_PATH \
            timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>/dev/null)
  else
    raw=$(AXEYUM_QINST_POSITIVE_PATH="$1" \
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
  case "$f" in
    /*) : ;;
    *)  f="$CORPUS$f" ;;
  esac
  # Arms alternate WITHIN the three passes too, so a drift in machine state
  # across the ~2.5 minutes a row takes does not land entirely on one arm.
  a1=$(one ""); b1=$(one "$VB")
  b2=$(one "$VB"); a2=$(one "")
  a3=$(one ""); b3=$(one "$VB")

  av="${a1%%/*} ${a2%%/*} ${a3%%/*}"
  bv="${b1%%/*} ${b2%%/*} ${b3%%/*}"
  a_dec=$(printf '%s\n' $av | grep -cE '^(sat|unsat)$')
  b_dec=$(printf '%s\n' $bv | grep -cE '^(sat|unsat)$')
  if [ "$a_dec" -eq 0 ] && [ "$b_dec" -eq 3 ]; then cls=STABLE-GAIN
  elif [ "$a_dec" -eq 3 ] && [ "$b_dec" -eq 0 ]; then cls=STABLE-LOSS
  else cls=UNSTABLE
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "${f#"$CORPUS"}" "$a1" "$a2" "$a3" "$b1" "$b2" "$b3" "$cls" >> "$OUT"
done < "$LIST"
echo "RECHECK-DONE -> $OUT"
