#!/usr/bin/env bash
# ADR-2132: re-run every MOVED row three times per arm, on ONE pinned core pair,
# at the same 24 s / 8 GiB envelope.
#
# Adapted from `bench-results/lra-warm-basis-20260916/recheck-movers.sh`, which
# is ADR-2125's, and the ADAPTATION is the two ARM VALUES: that script hardcodes
# `off` and `on`, and this lane's ship decision is `off` against `screened`.
# Passing them in is not a convenience -- a script that says `on` in its source
# while being used to score `screened` would put the right numbers under the
# wrong label, which is the one failure an A/B cannot see from its own output.
#
# [ADR-2100]'s original refuses unless the two BINARIES hash differently, because
# two identical arms give a perfect zero that looks exactly like agreement. Here
# both arms are one binary under two env values, so that risk moves to "the
# binary never reads the variable" -- and ADR-2125 PROVED that risk is real, its
# first mechanism check reading `warm_cube_checks=0` in BOTH arms. `ab3-run.sh
# --mechanism-check` is where that is refused, and it must have been run before
# this script's output means anything. Stated here rather than inherited.
#
# WHY three passes. A single interleaved pairing at 24 s carries a measured
# 1-1.5 % ambient flip rate on these boxes. ADR-1966 reported 25 raw movers and
# 22 after re-checking -- 11 of its 18 movers outside the treatment division
# VANISHED. The raw mover column is never the finding.
#
#   STABLE-GAIN      A never decided, B decided 3/3
#   STABLE-LOSS      A decided 3/3, B never decided
#   BOTH-DECIDE      both 3/3
#   NEITHER-DECIDES  both 0/3
#   UNSTABLE         anything else -- ambient, not an effect
#
# EXIT STATUS is recorded per pass as its own column: ADR-2045 measured
# `losses=0` by verdict with five new ABORTS underneath it.
#
# Usage: recheck-movers.sh <list> <out.tsv> <cores> <bin> <armA> <armB> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; ARM_A="$5"; ARM_B="$6"; BUDGET="${7:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -r "$LIST" ] || { echo "ABORT: $LIST unreadable"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }
# The two arms must DIFFER, for exactly ADR-2100's reason one level down: two
# identical env values give a perfect zero that reads as agreement.
[ "$ARM_A" = "$ARM_B" ] && { echo "ABORT: both arms are '$ARM_A'"; exit 2; }

one() {  # $1 = the lever value
  local raw rc v
  raw=$(AXEYUM_LRA_WARM_CUBE="$1" \
        timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>/dev/null)
  rc=$?
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s/%s' "${v:-none}" "$rc"
}

printf 'file\tarmA=%s\tA1\tA2\tA3\tarmB=%s\tB1\tB2\tB3\tverdict\n' "$ARM_A" "$ARM_B" > "$OUT"
n=0
while read -r rel; do
  [ -z "$rel" ] && continue
  f="$CORPUS$rel"
  [ -r "$f" ] || { echo "UNREADABLE $rel" >&2; continue; }
  n=$((n + 1))
  # Arms alternate WITHIN the three passes too, so a drift in machine state
  # across the ~2.5 minutes a row takes does not land entirely on one arm.
  a1=$(one "$ARM_A"); b1=$(one "$ARM_B")
  b2=$(one "$ARM_B"); a2=$(one "$ARM_A")
  a3=$(one "$ARM_A"); b3=$(one "$ARM_B")

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
  printf '%s\t\t%s\t%s\t%s\t\t%s\t%s\t%s\t%s\n' \
    "$rel" "$a1" "$a2" "$a3" "$b1" "$b2" "$b3" "$cls" >> "$OUT"
  echo "$cls $rel"
done < "$LIST"
echo "RECHECK-DONE $n rows -> $OUT"
