#!/usr/bin/env bash
# Run every gate-isolation probe (ADR-1955's and this lane's) through one
# binary and print `<verdict> <probe>` per line.
#
# The probes come in pairs differing in ONE token, so the table is only
# evidence when BOTH halves are run through the SAME binary in one invocation:
# a Real row read from one build and an Int row from another is not a pair.
#
# Usage: run-probes.sh <smtcomp_cli-binary> [timeout-ms]
set -eu
BIN="${1:?usage: run-probes.sh <binary> [timeout-ms]}"
TMO="${2:-24000}"
LANE="$(cd "$(dirname "$0")" && pwd)"

for f in "$LANE/../nested-array-ir-20260913/probes"/*.smt2 "$LANE/probes"/*.smt2; do
  v="$("$BIN" --timeout-ms "$TMO" "$f" 2>/dev/null | tail -1)"
  printf '%s\t%s\n' "$v" "$(basename "$f")"
done
