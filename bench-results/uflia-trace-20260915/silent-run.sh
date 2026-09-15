#!/usr/bin/env bash
# UFLIA-TRACE -- run `silent-split.py` over a list, one block per file.
#
#   silent-run.sh <list> <out.txt> <pin> <bin> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
HERE="$(cd "$(dirname "$0")" && pwd)"
: > "$OUT"
while IFS= read -r p; do
  [ -n "$p" ] || continue
  echo "==== $(basename "$p")" >> "$OUT"
  # AXEYUM_QPROBE_CENSUS is NOT optional here: without it every `rej_*` field
  # prints 0 and the per-class reason is unmeasured rather than absent.
  AXEYUM_QPROBE=1 AXEYUM_QPROBE_CENSUS=1 taskset -c "$PIN" timeout $((BUDGET + 40)) \
    "$AX" "$p" --timeout-ms $((BUDGET * 1000)) 2>&1 \
    | python3 "$HERE/silent-split.py" >> "$OUT"
done < "$LIST"
echo "DONE $OUT"
