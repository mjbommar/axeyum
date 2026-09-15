#!/usr/bin/env bash
# z3 4.13.3 on the Tier 1 pinned lists for UFNIA and AUFLIRA -- the two rows the
# 2026-09-15 gap table had no reference for. Same envelope as the board: 24 s
# wall, 8 GiB ulimit -v, one pinned core per worker, four workers on s4.
# Usage: run-z3.sh <DIV> <list> <out.tsv>
set -eu
DIV="$1"; LIST="$2"; OUT="$3"
ROOT=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental
CORES=(2 10 4 12)
one() {
  local f="$1" core="$2"
  local t0 t1 v rc
  t0=$(date +%s%N)
  # The lists carry ABSOLUTE paths. And z3 MUST get /dev/null on stdin: under
  # xargs the children inherit the list pipe, and z3 handed a bad path reads
  # stdin as SMT-LIB until the timeout -- 400 of 400 rows read `none` at 24 s
  # each on the first run of this script.
  local p="$f"; [ -f "$p" ] || p="$ROOT/$f"
  v=$( (ulimit -v 8388608; timeout --kill-after=5 24 taskset -c "$core" z3 -smt2 -T:23 "$p" </dev/null 2>/dev/null) | grep -m1 -oE '^(sat|unsat|unknown)$' || true); rc=$?
  t1=$(date +%s%N)
  printf '%s\t%s\t%s\t%s\n' "$f" "${v:-none}" "$(( (t1 - t0) / 1000000 ))" "z3-4.13.3"
}
export -f one; export ROOT
printf 'file\tz3\tms\tref\n' > "$OUT"
i=0
while read -r f; do echo "$f ${CORES[$((i % 4))]}"; i=$((i+1)); done < "$LIST" \
  | xargs -P 4 -L 1 bash -c 'one "$0" "$1"' >> "$OUT"
echo "DONE $DIV $(tail -n +2 "$OUT" | wc -l) rows" >> "$OUT.log"
