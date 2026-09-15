#!/usr/bin/env bash
# UFLIA-TRACE -- re-run every MOVED row three times per arm, ONE binary at TWO
# ENV VALUES, on one pinned core, at the same 24 s / 8 GiB envelope.
#
#   recheck-movers.sh <list> <out.tsv> <pin> <bin> <valueB> [budget_s]
#
# WHY. A single interleaved pairing at 24 s carries a measured 1-1.5 % ambient
# flip rate on these boxes. [ADR-1966] reported 25 raw movers and 22 after
# re-checking: **11 of its 18 movers outside the treatment division vanished**,
# and reporting the raw column would have overstated the effect by 11 files.
#
# Three passes per arm, and a row is classified only if all three agree:
#
#   STABLE-GAIN   A never decided, B decided 3/3
#   STABLE-LOSS   A decided 3/3, B never decided
#   UNSTABLE      anything else -- reported as ambient, not as an effect
#
# EXIT STATUS is recorded per pass as its own column: a run can report losses=0
# by verdict while creating new aborts underneath it.
#
# Arm A is the variable UNSET, not `=1`: an explicitly-set `1` and an unset
# variable take different paths through `cap_lever!`, and the arm that ships is
# the unset one.
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; VB="$5"; BUDGET="${6:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }
case "$VB" in
  ''|1|0) echo "ABORT: arm B value '$VB' is the shipped arm; both arms would be A"; exit 2 ;;
esac

one() {  # $1 = "" for the shipped arm, else the cap value
  local raw rc v
  if [ -z "$1" ]; then
    raw=$(env -u AXEYUM_QINST_TRIGGER_ALTERNATIVES \
            timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>/dev/null)
  else
    raw=$(AXEYUM_QINST_TRIGGER_ALTERNATIVES="$1" \
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
  # Arms alternate WITHIN the three passes too, so machine drift across the
  # ~2.5 minutes a row takes does not land entirely on one arm.
  a1=$(one ""); b1=$(one "$VB")
  b2=$(one "$VB"); a2=$(one "")
  a3=$(one ""); b3=$(one "$VB")

  av="${a1%%/*} ${a2%%/*} ${a3%%/*}"
  bv="${b1%%/*} ${b2%%/*} ${b3%%/*}"
  a_dec=$(printf '%s\n' $av | grep -cE '^(sat|unsat)$')
  b_dec=$(printf '%s\n' $bv | grep -cE '^(sat|unsat)$')
  if   [ "$a_dec" -eq 0 ] && [ "$b_dec" -eq 3 ]; then cls=STABLE-GAIN
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
