#!/usr/bin/env bash
# WRITER 3 of 3 (ADR-2102): the Tier 1 single-arm board run, appending to the
# outcome ledger.
#
# Mirrors `/nas3/data/axeyum/harness/postmerge-board-dt/scripts/board-run.sh`,
# the harness that produced `bench-results/tier1-current-20260914/*.tsv`. It is
# deliberately NOT an A/B: a lane's A/B measures its branch, this measures the
# tree that shipped.
#
# This is the runner `bench-results/dispatch-plan-sizing-20260915/README.md`
# dissected, and its two findings are exactly what this rewires:
#
#   1. "`board-run.sh` never persists a per-file raw output" -- it captures
#      stdout into a shell variable, greps ONE token, discards the rest. The
#      README then had to RE-RUN 645 undecided rows to recover what the sweep
#      had already computed.
#   2. "Even if `raw` had been kept, it would have carried no routing lines at
#      all" -- `board-run.sh` never passes `--trace`.
#
# Both are fixed in one place: `scripts/ledger-run-one.sh` runs with `--trace`
# and keeps the capture. This script formats no ledger row of its own.
#
# The `env -u AXEYUM_DATATYPE_NATIVE_REFUSAL` strip from the original is kept
# and is load-bearing: ADR-1980 ships `Decline` ON and the shipped arm is the
# UNSET environment, so a remote login shell that exported the variable would
# otherwise measure the historical arm silently.
#
# Usage: t1-board-run-ledger.sh <sweep-id> <division> <list> <out.tsv> <cores> \
#                               <bin> <sha> <capture-dir> [budget_s] [--invariance]
set -u

SWEEP="$1"; DIV="$2"; LIST="$3"; OUT="$4"; PIN="$5"; AX="$6"; SHA="$7"; CAPDIR="$8"
BUDGET="${9:-24}"
INVARIANCE="${10:-}"

REPO_ROOT="$(cd -- "$(dirname -- "$0")/../.." && pwd)"
RUNNER="$REPO_ROOT/scripts/ledger-run-one.sh"
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $DIV: $AX missing"; exit 2; }
[ -x "$RUNNER" ] || { echo "ABORT $DIV: $RUNNER missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $DIV: $OUT is non-empty; refusing to overwrite"; exit 2; }

INV_FLAG=()
[ "$INVARIANCE" = "--invariance" ] && INV_FLAG=(--no-trace-control)

mkdir -p "$CAPDIR"
printf 'file\tverdict\trc\tstatus\n' > "$OUT"
n=0
while read -r f; do
  [ -z "$f" ] && continue
  n=$((n + 1))
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  line=$(env -u AXEYUM_DATATYPE_NATIVE_REFUSAL "$RUNNER" \
    --sweep-id "$SWEEP" --arm "main" \
    --binary "$AX" --binary-sha "$SHA" \
    --file "$f" --corpus-root "$CORPUS" \
    --outdir "$CAPDIR" --core "$PIN" --budget-s "$BUDGET" \
    --note "tier1:$DIV" "${INV_FLAG[@]}" 2>>"$CAPDIR/$SWEEP.invariance.log")
  printf '%s\t%s\t%s\t%s\n' \
    "${f#"$CORPUS"}" \
    "$(printf '%s' "$line" | cut -f5)" \
    "$(printf '%s' "$line" | cut -f6)" \
    "${st:-none}" >> "$OUT"
done < "$LIST"
echo "T1-LEDGER-DONE $DIV rows=$n -> $OUT  bin=$SHA"
