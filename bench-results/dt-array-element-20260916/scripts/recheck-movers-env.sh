#!/usr/bin/env bash
# DT-ARRAY-ELEMENT -- `bench-results/route-ownership-20260915/recheck-movers.sh`
# with the two arms selected by an ENV VALUE instead of by two binaries.
#
# Everything about the METHOD is that script's, unchanged: three passes per arm
# on ONE pinned core at the same 24 s / 8 GiB envelope, arms alternated WITHIN
# the three passes so a drift in machine state does not land on one arm, a row
# classified only when all three agree, and the exit status of each pass kept as
# its own column (ADR-2045 measured `losses=0` by verdict with five new ABORTS
# underneath it).
#
# THE ONE GUARD THAT COULD NOT COME ACROSS, and what replaces it. The original
# refuses when `sha256sum` says both arms are the same binary -- a check that a
# one-binary/two-env A/B fails by construction. The property it was protecting
# is "the two arms are actually different", and here that is established by
# `arm-liveness.sh`, which shows the ON arm emitting ZERO of the W1 refusals the
# OFF arm emits on the same file. Do not read this script's output without that
# one having passed: an inert arm would classify every row BOTH-DECIDE or
# NEITHER-DECIDES and look like a clean null.
#
# Usage: recheck-movers-env.sh <list> <out.tsv> <core> <bin> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }

one() {  # $1 = "base" | "arm"
  local raw rc v
  if [ "$1" = base ]; then
    raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            env -u AXEYUM_DT_ARRAY_ELEMENT \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>/dev/null)
  else
    raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            env AXEYUM_DT_ARRAY_ELEMENT=on \
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
  a1=$(one base); b1=$(one arm)
  b2=$(one arm);  a2=$(one base)
  a3=$(one base); b3=$(one arm)

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
