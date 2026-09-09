#!/usr/bin/env bash
# Emit `<DIV>.regression-candidates.txt` for a division whose reconciliation
# residual is POSITIVE -- i.e. we decide fewer files than its ledger entry
# implies. The file lists the COMPLEMENT files still `unsolved` after the
# comp-confirm pass: every one of them was NOT on the 2026-09-05 loss list, so
# the ledger entry counted it as either `both` (a file we decided) or `neither`.
#
# The list is a superset of the regressions by exactly the ledger's `neither`
# count for that division; this sweep has no reference and therefore cannot say
# which members are which. Naming the superset is the honest artifact -- the
# alternative is naming nothing.
#
# Usage: regression-candidates.sh <DIV>
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
div="$1"
src="$here/../comp2/$div.tsv"
if [ ! -s "$src" ]; then src="$here/../comp/$div.tsv"; fi
awk -F'\t' 'NR > 1 && $3 == "unsolved" { print $1 }' "$src" \
  > "$here/../$div.regression-candidates.txt"
echo "$div $(wc -l < "$here/../$div.regression-candidates.txt") candidate(s) from $(basename "$(dirname "$src")")"
