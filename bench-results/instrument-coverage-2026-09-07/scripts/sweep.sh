#!/usr/bin/env bash
# Drives run_division.sh across all 12 bench-divisions-2026-09-07 divisions,
# in the same order and with the same 8-file-or-fewer selection, reproducing
# that lane's sample against the current (instrument-coverage) binary.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
BIN="$ROOT/target/release/examples/smtcomp_cli"
OUT_DIR="$ROOT/bench-results/instrument-coverage-2026-09-07"
LOG_DIR="$OUT_DIR/logs"
RUN="$ROOT/bench-results/instrument-coverage-2026-09-07/scripts/run_division.sh"

mkdir -p "$LOG_DIR"

DIVISIONS=(QF_ABV QF_BV QF_IDL QF_LIA QF_LRA QF_NIA QF_RDL QF_SLIA QF_UF QF_UFLIA UF QF_NRA)

echo "loadavg before: $(cat /proc/loadavg)" >&2

for DIV in "${DIVISIONS[@]}"; do
  if [ "$DIV" = "QF_NRA" ]; then
    LIST="$ROOT/bench-results/parity-losses-20260906/QF_NRA.txt"
  else
    LIST="$ROOT/bench-results/parity-losses-20260905/${DIV}.txt"
  fi
  OUT_TSV="$OUT_DIR/${DIV}.tsv"
  "$RUN" "$DIV" "$LIST" "$BIN" "$OUT_TSV" "$LOG_DIR" 8
done

echo "loadavg after: $(cat /proc/loadavg)" >&2
echo "sweep done" >&2
