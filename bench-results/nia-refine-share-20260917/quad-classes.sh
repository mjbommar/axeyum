#!/usr/bin/env bash
# The 2x2 on the scoring files: ONE binary under FOUR env settings, three
# passes per arm, arms interleaved within each pass so a drift in machine
# state does not land on one arm. Lane A13-NIA, ADR-2148.
#
# Arms (lemmas x share):
#   L2S0  AXEYUM_NIA_ORDER_LEMMAS=0 AXEYUM_NIA_REFINE_SHARE=0   shipped
#   L2S3  AXEYUM_NIA_ORDER_LEMMAS=1 AXEYUM_NIA_REFINE_SHARE=0   lemmas, old share
#   L3S0  AXEYUM_NIA_ORDER_LEMMAS=0 AXEYUM_NIA_REFINE_SHARE=3   no lemmas, new share
#   L3S3  AXEYUM_NIA_ORDER_LEMMAS=1 AXEYUM_NIA_REFINE_SHARE=3   ADR-2136's B arm
#
# Per arm the three verdicts are recorded as `v/rc` each; a row is DECIDED
# for an arm only when all three passes decide (sat/unsat), UNDECIDED when
# none does, MIXED otherwise. Timing via $EPOCHREALTIME only (uutils date).
#
# usage: a13-nia-quad.sh <list> <out.tsv> <core> <bin> [budget_s]
set -u
LIST=$1; OUT=$2; PIN=$3; AX=$4; BUDGET=${5:-24}
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }

# Clock self-check: uutils `date` prints ns for %3N; $EPOCHREALTIME is the unit.
t0=$EPOCHREALTIME; sleep 0.2; t1=$EPOCHREALTIME
ms=$(python3 -c "print(int(($t1-$t0)*1000))")
{ [ "$ms" -ge 150 ] && [ "$ms" -le 400 ]; } || { echo "ABORT: clock self-check ${ms} ms"; exit 3; }

ARM_L2S0="AXEYUM_NIA_ORDER_LEMMAS=2 AXEYUM_NIA_REFINE_SHARE=0"
ARM_L2S3="AXEYUM_NIA_ORDER_LEMMAS=2 AXEYUM_NIA_REFINE_SHARE=3"
ARM_L3S0="AXEYUM_NIA_ORDER_LEMMAS=3 AXEYUM_NIA_REFINE_SHARE=0"
ARM_L3S3="AXEYUM_NIA_ORDER_LEMMAS=3 AXEYUM_NIA_REFINE_SHARE=3"
HASH=$(sha256sum "$AX" | cut -d' ' -f1)

one() {  # $1 = env assignment list
  local raw rc v s0 s1
  s0=$EPOCHREALTIME
  # shellcheck disable=SC2086
  raw=$(env $1 timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>/dev/null)
  rc=$?
  s1=$EPOCHREALTIME
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s/%s/%s' "${v:-none}" "$rc" "$(python3 -c "print(int(($s1-$s0)*1000))")"
}

classify() {  # $1 $2 $3 = v/rc/ms
  local d=0 r
  for r in "$1" "$2" "$3"; do case "${r%%/*}" in sat|unsat) d=$((d+1));; esac; done
  case $d in 3) echo DECIDED;; 0) echo UNDECIDED;; *) echo MIXED;; esac
}

printf 'file\tL2S0_1\tL2S0_2\tL2S0_3\tL2S3_1\tL2S3_2\tL2S3_3\tL3S0_1\tL3S0_2\tL3S0_3\tL3S3_1\tL3S3_2\tL3S3_3\tL2S0\tL2S3\tL3S0\tL3S3\n' > "$OUT"
n=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  n=$((n+1))
  a1=$(one "$ARM_L2S0"); b1=$(one "$ARM_L2S3"); c1=$(one "$ARM_L3S0"); d1=$(one "$ARM_L3S3")
  d2=$(one "$ARM_L3S3"); c2=$(one "$ARM_L3S0"); b2=$(one "$ARM_L2S3"); a2=$(one "$ARM_L2S0")
  a3=$(one "$ARM_L2S0"); b3=$(one "$ARM_L2S3"); c3=$(one "$ARM_L3S0"); d3=$(one "$ARM_L3S3")
  ca=$(classify "$a1" "$a2" "$a3"); cb=$(classify "$b1" "$b2" "$b3")
  cc=$(classify "$c1" "$c2" "$c3"); cd=$(classify "$d1" "$d2" "$d3")
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$f" "$a1" "$a2" "$a3" "$b1" "$b2" "$b3" "$c1" "$c2" "$c3" "$d1" "$d2" "$d3" \
    "$ca" "$cb" "$cc" "$cd" >> "$OUT"
  printf 'quad %d: L2S0=%s L2S3=%s L3S0=%s L3S3=%s %s\n' "$n" "$ca" "$cb" "$cc" "$cd" "${f##*/}" >&2
done < "$LIST"
echo "QUAD-DONE $n rows -> $OUT bin=$HASH"
