#!/usr/bin/env bash
# Interleaved per-file A/B of TWO BINARIES for ADR-2100.
#
# ADR-2100 is not a lever: the ownership rule is unconditional code, so there is
# no env value to flip and the two arms have to be two builds. That makes one
# failure mode possible that a one-binary A/B cannot have -- **the same binary
# in both arms**, which produces a perfect zero that looks exactly like
# agreement. This script REFUSES unless the two binaries hash differently
# (ADR-2060's runner established the check after the same risk).
#
#   A = main at the branch's merge-base (the shipped ladder)
#   B = this branch (typed route ownership)
#
# Both arms run BACK TO BACK on the SAME file on the SAME pinned core, so ambient
# load -- which has moved 23 verdicts in one division at fixed code on these
# boxes -- cancels in the DIFFERENCE rather than landing entirely on whichever
# arm ran second. Arm order alternates per file for the same reason.
#
# EXIT STATUS is recorded per arm as its own column, not folded into the verdict:
# ADR-2045 measured `losses=0` by verdict and five new ABORTS underneath it.
#
# Same envelope as every board here: 24 s wall, 8 GiB `ulimit -v`, one pinned
# physical core pair.
#
# Usage: ab-run.sh <tag> <list> <out.tsv> <cores> <binA> <binB> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX_A="$5"; AX_B="$6"; BUDGET="${7:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX_A" ] || { echo "ABORT $TAG: $AX_A missing"; exit 2; }
[ -x "$AX_B" ] || { echo "ABORT $TAG: $AX_B missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }

HA=$(sha256sum "$AX_A" | cut -d' ' -f1)
HB=$(sha256sum "$AX_B" | cut -d' ' -f1)
if [ "$HA" = "$HB" ]; then
  echo "ABORT $TAG: both arms are the SAME binary ($HA)."
  echo "  Two identical arms make every number in this run vacuous while looking"
  echo "  exactly like agreement. Build the two commits separately."
  exit 2
fi

run_arm() {  # $1 = path to the binary
  local t0 t1 raw rc v
  t0=$(date +%s%N)
  raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
          "$1" "$f" 2>/dev/null)
  rc=$?
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s\t%s\t%s' "${v:-none}" "$(( (t1 - t0) / 1000000 ))" "$rc"
}

printf 'file\tA\tA_ms\tA_rc\tB\tB_ms\tB_rc\tfirst\tstatus\n' > "$OUT"
n=0
while read -r f; do
  [ -z "$f" ] && continue
  n=$((n + 1))
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  if [ $((n % 2)) -eq 1 ]; then
    first=A; a=$(run_arm "$AX_A"); b=$(run_arm "$AX_B")
  else
    first=B; b=$(run_arm "$AX_B"); a=$(run_arm "$AX_A")
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "${f#"$CORPUS"}" "$a" "$b" "$first" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "AB-DONE $TAG $n files -> $OUT  A=$HA B=$HB"
