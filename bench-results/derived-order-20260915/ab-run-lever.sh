#!/usr/bin/env bash
# Interleaved per-file A/B of ONE binary under TWO env values, for ADR-2106.
#
# `bench-results/route-ownership-20260915/ab-run.sh` with one difference, stated
# here because a runner that silently diverges from the one it copies is how a
# comparison stops comparing: ADR-2100 was unconditional code, so its two arms
# had to be two BUILDS and its refusal is "both arms are the same binary".
# ADR-2106 is a LEVER, so both arms are the same binary by construction and the
# refusal moves to the thing that can actually be degenerate here -- **the same
# env value in both arms**, which produces a perfect zero that looks exactly
# like agreement.
#
#   A = AXEYUM_LADDER_ORDER=$ENV_A   (`hand`, the shipped order)
#   B = AXEYUM_LADDER_ORDER=$ENV_B   (`derived`, the ledger's order)
#
# One binary is strictly BETTER evidence than two here, not a shortcut: with two
# builds the arms differ by a compiler invocation as well as by the change, and
# the runner can only hash-check that they differ at all.
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
# Usage: ab-run-lever.sh <tag> <list> <out.tsv> <cores> <bin> <envA> <envB> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX="$5"; ENV_A="$6"; ENV_B="$7"; BUDGET="${8:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }

if [ "$ENV_A" = "$ENV_B" ]; then
  echo "ABORT $TAG: both arms set AXEYUM_LADDER_ORDER=$ENV_A."
  echo "  Two identical arms make every number in this run vacuous while looking"
  echo "  exactly like agreement. Name two different orders."
  exit 2
fi

HASH=$(sha256sum "$AX" | cut -d' ' -f1)

run_arm() {  # $1 = AXEYUM_LADDER_ORDER value
  local t0 t1 raw rc v
  t0=$(date +%s%N)
  raw=$(AXEYUM_LADDER_ORDER="$1" timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>/dev/null)
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
    first=A; a=$(run_arm "$ENV_A"); b=$(run_arm "$ENV_B")
  else
    first=B; b=$(run_arm "$ENV_B"); a=$(run_arm "$ENV_A")
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "${f#"$CORPUS"}" "$a" "$b" "$first" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "AB-DONE $TAG $n files -> $OUT  bin=$HASH A=$ENV_A B=$ENV_B"
