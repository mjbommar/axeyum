#!/usr/bin/env bash
# QUANT-INSTANCE-PROBE steps 3/4: run OUR release binary on every ground-only
# file in <dir>/*.ground.smt2, through ledger-run-one.sh (ADR-2102 outcome
# ledger), pinned, 24s/8GiB.
#
#   qip-run-ours.sh <ground_dir> <arm> <pin> <repo>
set -u
GDIR="$1"; ARM="$2"; PIN="$3"; REPO="$4"
BIN="$REPO/target/release/examples/smtcomp_cli"
SHA=$(sha256sum "$BIN" | cut -d' ' -f1)
OUTDIR="$REPO/bench-results/quant-instance-probe-20260916/runs/$ARM"
mkdir -p "$OUTDIR"

for f in "$GDIR"/*.ground.smt2; do
  [ -f "$f" ] || continue
  bash "$REPO/scripts/ledger-run-one.sh" \
    --sweep-id quant-instance-probe \
    --arm "$ARM" \
    --binary "$BIN" \
    --binary-sha "$SHA" \
    --file "$f" \
    --corpus-root "$GDIR/" \
    --outdir "$OUTDIR" \
    --budget-s 24 --headroom-s 16 --vlimit-kb $((8 * 1024 * 1024)) \
    --core "$PIN" --host s6
done
echo "DONE $OUTDIR"
