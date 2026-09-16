#!/usr/bin/env bash
# Drive one shard of the ADR-2134 A/B across every population, sequentially, on
# one pinned core pair.
#
# Two things are priced and they need different runners (see `ab-run.sh`'s
# header): the `algebraic-witness` ARM is an env value, while the
# `RealAlgebraic::sign_at` exactness fix is not behind any lever and needs the
# BASELINE binary against the new one at the same arm.
#
# Output file names carry the shard AND the sweep kind, so two runs of this
# script on different shards cannot write the same file. That is not
# hypothetical: this lane's first sizing run launched one shard twice and the
# duplicate truncated the first run's output while rewriting it. A fixed output
# name shared by two invocations is the defect; a decreasing row count is the
# cheapest detector.
set -u

SHARD=""; CORE=""; BIN=""; BIN_A=""; OUTDIR="."
CORPUS_ROOT="/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental"
BUDGET_S=24

while [ $# -gt 0 ]; do
  case "$1" in
    --shard) SHARD="$2"; shift 2 ;;
    --core) CORE="$2"; shift 2 ;;
    --binary) BIN="$2"; shift 2 ;;
    --baseline) BIN_A="$2"; shift 2 ;;
    --outdir) OUTDIR="$2"; shift 2 ;;
    --corpus-root) CORPUS_ROOT="$2"; shift 2 ;;
    --budget-s) BUDGET_S="$2"; shift 2 ;;
    *) echo "ab-sweep: unknown argument $1" >&2; exit 2 ;;
  esac
done
for required in SHARD CORE BIN BIN_A; do
  if [ -z "${!required}" ]; then echo "ab-sweep: --${required,,} required" >&2; exit 2; fi
done

here="$(cd "$(dirname "$0")" && pwd)"
done_file="$OUTDIR/ab-sweep-shard${SHARD}.done"
: > "$done_file"

run() {  # $1 label, then ab-run.sh arguments
  local label="$1"; shift
  "$here/ab-run.sh" "$@" > "$OUTDIR/${label}-shard${SHARD}.log" 2>&1
  echo "$label shard$SHARD EXIT=$?" >> "$done_file"
}

# 1. THE LEVER: one binary, two env values. `single-cell` is the shipped
#    default, `algebraic-witness` differs from it in exactly one policy field.
for pop in qfnra qfnia qflra heldout; do
  run "lever-${pop}" \
    --binary "$BIN" --list "$OUTDIR/${pop}-shard${SHARD}.txt" \
    --shard "$SHARD" --core "$CORE" --budget-s "$BUDGET_S" \
    --corpus-root "$CORPUS_ROOT" \
    --arm-a single-cell --arm-b algebraic-witness \
    --out "$OUTDIR/lever-${pop}-shard${SHARD}.tsv"
done

# 2. THE EXACTNESS FIX: two binaries, the SAME arm. This is the only way to
#    price a change that is not behind a lever.
for pop in qfnra qflra; do
  run "exactness-${pop}" \
    --binary "$BIN" --binary-a "$BIN_A" \
    --list "$OUTDIR/${pop}-shard${SHARD}.txt" \
    --shard "$SHARD" --core "$CORE" --budget-s "$BUDGET_S" \
    --corpus-root "$CORPUS_ROOT" \
    --arm-a single-cell --arm-b single-cell \
    --out "$OUTDIR/exactness-${pop}-shard${SHARD}.tsv"
done

echo "ALLDONE" >> "$done_file"
