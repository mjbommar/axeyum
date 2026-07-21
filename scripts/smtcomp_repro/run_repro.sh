#!/usr/bin/env bash
# Canonical local reproduction of the SMT-COMP scoring pipeline.
#
# Builds the axeyum SMT-COMP CLI, then scores axeyum against the staged
# reference solvers (cvc5, bitwuzla) on a chosen division, printing the full
# SMT-COMP scoreboard. Reference solver binaries live in the gitignored
# references/smtcomp-solvers/ (staged once; never committed, never PR'd).
#
# Usage:
#   scripts/smtcomp_repro/run_repro.sh <corpus_dir> [wall_s] [limit] [track]
# Example:
#   scripts/smtcomp_repro/run_repro.sh corpus/qfbv-curated 20 40 single_query
set -euo pipefail

CORPUS="${1:-corpus/qfbv-curated}"
WALL="${2:-20}"
LIMIT="${3:-40}"
TRACK="${4:-single_query}"

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"

CLI="target/release/examples/smtcomp_cli"
SOL="references/smtcomp-solvers"

echo ">> building axeyum SMT-COMP CLI (release)"
cargo build --release -q -p axeyum-bench --example smtcomp_cli

SOLVERS=(--solver "axeyum=$CLI")
[ -x "$SOL/cvc5" ]     && SOLVERS+=(--solver "cvc5=$SOL/cvc5")
[ -x "$SOL/bitwuzla" ] && SOLVERS+=(--solver "bitwuzla=$SOL/bitwuzla")

INT_TIMEOUT=$(( WALL * 1000 - 1000 ))
OUT="/tmp/smtcomp_repro_$(basename "$CORPUS")_${TRACK}.json"

echo ">> running competition: corpus=$CORPUS T=${WALL}s limit=$LIMIT track=$TRACK"
python3 scripts/smtcomp_repro/compete.py \
  --corpus "$CORPUS" \
  "${SOLVERS[@]}" \
  --track "$TRACK" --wall-limit "$WALL" --internal-timeout-ms "$INT_TIMEOUT" \
  --limit "$LIMIT" --out "$OUT"

echo ">> scoreboard JSON: $OUT"
