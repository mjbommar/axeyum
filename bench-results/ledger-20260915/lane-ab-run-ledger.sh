#!/usr/bin/env bash
# WRITER 1 of 3 (ADR-2102): the per-lane interleaved A/B, appending to the
# outcome ledger.
#
# Mirrors `bench-results/route-ownership-20260915/ab-run.sh` (ADR-2100) -- the
# newest and most complete of the three runner shapes: two binaries, back to
# back on the same file on the same pinned core, order alternating per file,
# exit status recorded as its own column, and a REFUSAL when the two arms hash
# the same (two identical arms produce a perfect zero that looks exactly like
# agreement).
#
# The one difference is the capture. `ab-run.sh` does
#
#     raw=$(timeout ... "$AX" "$f" ...); v=$(printf '%s\n' "$raw" | grep -m1 ...)
#
# and keeps the token. This calls `scripts/ledger-run-one.sh`, which runs the
# same command under the same envelope WITH `--trace`, keeps the stdout as a
# file, and appends one ledger row through `scripts/outcome_ledger.py`. This
# script therefore formats no ledger row itself -- which is what makes schema
# drift at a writer unreachable rather than merely tested for.
#
# **This does not replace the A/B.** The TSV below is still the instrument a
# claim is made from; the ledger is the record beside it. A delta computed
# between two single-arm ledger runs at different loads is the 77/79/85 error
# with a database in front of it.
#
# Usage: lane-ab-run-ledger.sh <sweep-id> <list> <out.tsv> <cores> <binA> <shaA> \
#                              <binB> <shaB> <capture-dir> [budget_s] [--invariance]
set -u

SWEEP="$1"; LIST="$2"; OUT="$3"; PIN="$4"
AX_A="$5"; SHA_A="$6"; AX_B="$7"; SHA_B="$8"; CAPDIR="$9"
BUDGET="${10:-24}"
INVARIANCE="${11:-}"

REPO_ROOT="$(cd -- "$(dirname -- "$0")/../.." && pwd)"
RUNNER="$REPO_ROOT/scripts/ledger-run-one.sh"
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX_A" ] || { echo "ABORT $SWEEP: $AX_A missing"; exit 2; }
[ -x "$AX_B" ] || { echo "ABORT $SWEEP: $AX_B missing"; exit 2; }
[ -x "$RUNNER" ] || { echo "ABORT $SWEEP: $RUNNER missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $SWEEP: $OUT is non-empty; refusing to overwrite"; exit 2; }

HA=$(sha256sum "$AX_A" | cut -d' ' -f1)
HB=$(sha256sum "$AX_B" | cut -d' ' -f1)
if [ "$HA" = "$HB" ]; then
  echo "ABORT $SWEEP: both arms are the SAME binary ($HA)."
  echo "  Two identical arms make every number in this run vacuous while looking"
  echo "  exactly like agreement. Build the two commits separately."
  exit 2
fi
if [ "$SHA_A" = "$SHA_B" ]; then
  echo "ABORT $SWEEP: both arms claim commit $SHA_A. The ledger's binary_sha is"
  echo "  what separates the arms on read; two rows claiming one commit are not"
  echo "  an A/B, they are a doubled single-arm run."
  exit 2
fi

INV_FLAG=()
[ "$INVARIANCE" = "--invariance" ] && INV_FLAG=(--no-trace-control)

run_arm() {  # $1 = arm label, $2 = binary, $3 = commit sha; prints "verdict\trc"
  local line
  line=$("$RUNNER" \
    --sweep-id "$SWEEP" --arm "$1" \
    --binary "$2" --binary-sha "$3" \
    --file "$f" --corpus-root "$CORPUS" \
    --outdir "$CAPDIR" --core "$PIN" --budget-s "$BUDGET" \
    --note "lane-ab" "${INV_FLAG[@]}" 2>>"$CAPDIR/$SWEEP.invariance.log")
  # Fields 5 and 6 of `LEDGER-ROW\t<sweep>\t<arm>\t<rel>\t<verdict>\t<rc>`.
  printf '%s\t%s' "$(printf '%s' "$line" | cut -f5)" "$(printf '%s' "$line" | cut -f6)"
}

mkdir -p "$CAPDIR"
printf 'file\tA\tA_rc\tB\tB_rc\tfirst\tstatus\n' > "$OUT"
n=0
while read -r f; do
  [ -z "$f" ] && continue
  n=$((n + 1))
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  if [ $((n % 2)) -eq 1 ]; then
    first=A; a=$(run_arm A "$AX_A" "$SHA_A"); b=$(run_arm B "$AX_B" "$SHA_B")
  else
    first=B; b=$(run_arm B "$AX_B" "$SHA_B"); a=$(run_arm A "$AX_A" "$SHA_A")
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "${f#"$CORPUS"}" "$a" "$b" "$first" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "AB-LEDGER-DONE $SWEEP $n files -> $OUT  A=$HA($SHA_A) B=$HB($SHA_B)"
