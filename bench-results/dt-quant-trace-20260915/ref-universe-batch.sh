#!/usr/bin/env bash
# DT-QUANT-TRACE -- `ref-universe.sh` over the cores we refuse on a datatype
# construct, with the counters and the control on one line each.
#
#   ref-universe-batch.sh <list-of-.smt2> [tlimit_s]
set -u
LIST="$1"; TL="${2:-20}"
HERE="$(cd "$(dirname "$0")" && pwd)"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  echo "##### $(basename "$f")"
  "$HERE/ref-universe.sh" "$f" "$TL" 2>&1 \
    | grep -E '^(sat|unsat|unknown|timeout)$|datatype-|quant-inst|max-generation|matching lines|total lines'
done < "$LIST"
