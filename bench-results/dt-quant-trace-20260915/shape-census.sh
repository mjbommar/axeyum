#!/usr/bin/env bash
# DT-QUANT-TRACE -- run the construct classifier over a list of .smt2 files.
#
#   shape-census.sh <list-of-paths> <out.tsv>
#
# `ulimit -v` bounds ADDRESS SPACE, which `timeout` does not: CLAUDE.md records
# a lane's `let`-expander reaching 63.4 GB on exactly this corpus and taking the
# host down.  `dtshape.py` resolves `let` rather than expanding it, so the cap
# is a belt on a design that already does not blow up -- and it is here so the
# next person to change that design finds a ceiling rather than an OOM.
#
# The classifier's own exit status depends on its finding (a parse failure is
# rc 3), and it is carried out of here rather than swallowed.
set -u
LIST="$1"; OUT="$2"
HERE="$(cd "$(dirname "$0")" && pwd)"
( ulimit -v 16000000; xargs -a "$LIST" -r python3 "$HERE/dtshape.py" ) > "$OUT"
rc=$?
echo "shape-census rc=$rc rows=$(( $(wc -l < "$OUT") - 1 )) -> $OUT"
exit "$rc"
