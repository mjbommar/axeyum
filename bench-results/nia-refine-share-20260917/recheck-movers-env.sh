#!/usr/bin/env bash
# Re-run every MOVED row three times per arm, ONE binary under TWO ENV
# SETTINGS, on one pinned core, at the same 24 s / 8 GiB envelope.
# Lane NIA-ORDER-LEMMAS, ADR-2136.
#
# `bench-results/route-ownership-20260915/recheck-movers.sh` is the original and
# its logic is reproduced verbatim; the one change is that it takes two
# BINARIES and refuses when their hashes match, which an env-lever A/B can
# never satisfy. This takes two `VAR=VAL` assignment lists instead and keeps
# the equivalent refusal: two identical arms produce a perfect zero that looks
# exactly like agreement.
#
# WHY IT EXISTS AT ALL. A single interleaved pairing at 24 s carries a measured
# 1-1.5 % ambient flip rate on these boxes. ADR-1966 reported 25 raw movers and
# 22 after re-checking: 11 of its 18 movers outside the treatment division
# vanished, and reporting the raw column would have overstated the effect by 11
# files. So a raw mover is a candidate, never a result.
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
# Usage: recheck-movers-env.sh <list> <out.tsv> <core> <bin> <envA> <envB> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; ENV_A="$5"; ENV_B="$6"; BUDGET="${7:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }
if [ "$ENV_A" = "$ENV_B" ]; then
    echo "ABORT: both arms set [$ENV_A]."
    echo "  Two identical arms make every number vacuous while looking exactly"
    echo "  like agreement. Name two different settings."
    exit 2
fi

HASH=$(sha256sum "$AX" | cut -d' ' -f1)

one() {  # $1 = env assignment list (may be empty)
  local raw rc v
  # shellcheck disable=SC2086  # $1 is a deliberate word-split assignment list
  raw=$(env $1 timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>/dev/null)
  rc=$?
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s/%s' "${v:-none}" "$rc"
}

printf 'file\tA1\tA2\tA3\tB1\tB2\tB3\tverdict\n' > "$OUT"
n=0
while read -r f; do
  [ -z "$f" ] && continue
  n=$((n + 1))
  # Arms alternate WITHIN the three passes too, so a drift in machine state
  # across the ~2.5 minutes a row takes does not land entirely on one arm.
  a1=$(one "$ENV_A"); b1=$(one "$ENV_B")
  b2=$(one "$ENV_B"); a2=$(one "$ENV_A")
  a3=$(one "$ENV_A"); b3=$(one "$ENV_B")

  decided() { case "${1%%/*}" in sat|unsat) return 0;; *) return 1;; esac; }
  a_dec=0; for r in "$a1" "$a2" "$a3"; do decided "$r" && a_dec=$((a_dec + 1)); done
  b_dec=0; for r in "$b1" "$b2" "$b3"; do decided "$r" && b_dec=$((b_dec + 1)); done
  if [ "$a_dec" -eq 0 ] && [ "$b_dec" -eq 3 ]; then
      v=STABLE-GAIN
  elif [ "$a_dec" -eq 3 ] && [ "$b_dec" -eq 0 ]; then
      v=STABLE-LOSS
  else
      v=UNSTABLE
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
      "$f" "$a1" "$a2" "$a3" "$b1" "$b2" "$b3" "$v" >> "$OUT"
  printf 'recheck %d: %s %s\n' "$n" "$v" "$f" >&2
done < "$LIST"
echo "RECHECK-DONE $n rows -> $OUT  bin=$HASH A=[$ENV_A] B=[$ENV_B]"
