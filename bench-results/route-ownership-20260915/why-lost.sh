#!/usr/bin/env bash
# For each row the 3x-per-arm re-check classified STABLE-LOSS, print BOTH arms'
# `--trace` route summary lines side by side.
#
# A loss count is not a diagnosis. ADR-1966 had to read the trail to find that
# its `UFLIA` control's one loss was `q:egraph` eating 19.3 s of the budget that
# `q:mbqi-quick` had needed, and that is a different fact from "the change lost a
# file" -- it says the cost is NOT confined to the queries whose refusal the
# change converts. Same envelope as the A/B: 24 s, 8 GiB, one pinned core.
#
# Usage: why-lost.sh <list> <cores> <binA> <binB> [budget_s]
set -u
LIST="$1"; PIN="$2"; AX_A="$3"; AX_B="$4"; BUDGET="${5:-24}"
VLIM=$((8 * 1024 * 1024))

arm() {  # $1 = binary, $2 = label
  local raw
  raw=$(AXEYUM_TRACE=1 timeout $((BUDGET + 16)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
          "$1" "$f" 2>/dev/null)
  printf '  %s verdict=%s\n' "$2" \
    "$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')"
  # BOTH prefixes: the watchdog path prints `; partial route ` (ADR-2075), and a
  # loss is exactly the kind of row that takes it.
  printf '%s\n' "$raw" | grep -E '^; (partial )?route |^; give-up ' | sed 's/^/  /'
}

while read -r f; do
  [ -z "$f" ] && continue
  echo "=== ${f##*/}"
  arm "$AX_A" "A"
  arm "$AX_B" "B"
done < "$LIST"
echo "WHY-LOST-DONE"
