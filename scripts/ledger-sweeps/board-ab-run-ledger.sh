#!/usr/bin/env bash
# WRITER 2 of 3 (ADR-2102): the 16-division board A/B, appending to the outcome
# ledger.
#
# Mirrors `/nas3/data/axeyum/harness/postmerge-board-dt/scripts/ab-two-bins.sh`,
# which produced `bench-results/board-ab-20260915/*.tsv` (`2611e14b0` against
# `054104068`, 16 divisions x 200 files, 2,419 -> 2,419). Same interleaving,
# same envelope, same alternating order.
#
# Two differences, both of them the point of this phase:
#
#  1. The capture is kept. `ab-two-bins.sh` does `raw=$(...)`, greps one token
#     out of it and drops the rest -- and never passes `--trace`, so there was
#     nothing in it to drop anyway. That board's README ends with a caveat that
#     the population "is not reconstructible from what is committed"; a ledger
#     row carries the corpus-RELATIVE path, so it is.
#  2. `rc` becomes a real column. `ab-two-bins.sh` records verdict and ms and
#     not the exit status, which is exactly the hole ADR-2045 found underneath
#     `losses=0`: five new ABORTS invisible in a verdict comparison.
#
# The board's own TSV is still written, in the original's column order plus
# `rc`, so the existing summarizers keep working. This is an addition to the
# board, not a replacement for it.
#
# Usage: board-ab-run-ledger.sh <sweep-id> <division> <list> <out.tsv> <cores> \
#                               <binA> <shaA> <binB> <shaB> <capture-dir> [budget_s] [--invariance]
set -u

SWEEP="$1"; DIV="$2"; LIST="$3"; OUT="$4"; PIN="$5"
AX_A="$6"; SHA_A="$7"; AX_B="$8"; SHA_B="$9"; CAPDIR="${10}"
BUDGET="${11:-24}"
INVARIANCE="${12:-}"
INV_FLAG=()
[ "$INVARIANCE" = "--invariance" ] && INV_FLAG=(--no-trace-control)

REPO_ROOT="$(cd -- "$(dirname -- "$0")/../.." && pwd)"
RUNNER="$REPO_ROOT/scripts/ledger-run-one.sh"
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX_A" ] || { echo "ABORT $DIV: $AX_A missing"; exit 2; }
[ -x "$AX_B" ] || { echo "ABORT $DIV: $AX_B missing"; exit 2; }
[ -x "$RUNNER" ] || { echo "ABORT $DIV: $RUNNER missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $DIV: $OUT non-empty"; exit 2; }

HA=$(sha256sum "$AX_A" | cut -d' ' -f1)
HB=$(sha256sum "$AX_B" | cut -d' ' -f1)
[ "$HA" = "$HB" ] && { echo "ABORT $DIV: both arms are the SAME binary ($HA)"; exit 2; }

mkdir -p "$CAPDIR"

run_arm() {  # $1 = arm label, $2 = binary, $3 = commit sha
  local line
  line=$("$RUNNER" \
    --sweep-id "$SWEEP" --arm "$1" \
    --binary "$2" --binary-sha "$3" \
    --file "$f" --corpus-root "$CORPUS" \
    --outdir "$CAPDIR" --core "$PIN" --budget-s "$BUDGET" \
    --note "board-ab:$DIV" "${INV_FLAG[@]}" 2>>"$CAPDIR/$SWEEP.invariance.log")
  printf '%s\t%s' "$(printf '%s' "$line" | cut -f5)" "$(printf '%s' "$line" | cut -f6)"
}

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
echo "BOARD-AB-LEDGER-DONE $DIV rows=$n -> $OUT  A=$SHA_A B=$SHA_B"
