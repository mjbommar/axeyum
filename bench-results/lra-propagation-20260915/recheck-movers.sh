#!/usr/bin/env bash
# ADR-2122: re-run every MOVED row three times per arm, on ONE pinned core pair,
# at the same 24 s / 8 GiB envelope.
#
# Adapted from `bench-results/route-ownership-20260915/recheck-movers.sh`, and
# the adaptation is the guard: that script refuses unless the two BINARIES hash
# differently, because two identical arms give a perfect zero that looks exactly
# like agreement. This lane's arms are one binary under two env values, so the
# same risk moves to "the binary never reads the variable". `--mechanism-check`
# in `ab-run.sh` is where that is refused; this script requires it to have been
# run and says so rather than silently inheriting the older guard's reassurance.
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
# Usage: recheck-movers.sh <list-of-relative-paths> <out.tsv> <cores> <bin> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -r "$LIST" ] || { echo "ABORT: $LIST unreadable"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }

one() {  # $1 = the lever value
  local raw rc v
  raw=$(AXEYUM_LRA_BOUND_PROPAGATION="$1" \
        timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>/dev/null)
  rc=$?
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s/%s' "${v:-none}" "$rc"
}

printf 'file\tA1\tA2\tA3\tB1\tB2\tB3\tverdict\n' > "$OUT"
n=0
while read -r rel; do
  [ -z "$rel" ] && continue
  f="$CORPUS$rel"
  [ -r "$f" ] || { echo "UNREADABLE $rel" >&2; continue; }
  n=$((n + 1))
  # Arms alternate WITHIN the three passes too, so a drift in machine state
  # across the ~2.5 minutes a row takes does not land entirely on one arm.
  a1=$(one off); b1=$(one on)
  b2=$(one on);  a2=$(one off)
  a3=$(one off); b3=$(one on)

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
    "$rel" "$a1" "$a2" "$a3" "$b1" "$b2" "$b3" "$cls" >> "$OUT"
  echo "$cls $rel"
done < "$LIST"
echo "RECHECK-DONE $n rows -> $OUT"
