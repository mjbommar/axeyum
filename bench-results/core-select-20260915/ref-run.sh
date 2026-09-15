#!/usr/bin/env bash
# CORE-SELECT -- the REFERENCE verdict for one shard's files (R2).
#
#   ref-run.sh <list> <out.tsv> <pin> [budget_s] [corpus]
#
# Uses a reference solver to find the core, not ours: ours is the thing that
# fails.  Plain `z3 -T:N` first -- `:produce-unsat-cores` disables preprocessing
# and can turn an `unsat` into an `unknown`, so asking for the core up front
# would manufacture `REF-NONE` rows.  The core is extracted separately, only on
# the rows this pass calls `unsat`.
#
# Columns: file, z3 verdict, exit status, ms, the file's own declared :status,
# host, core.  The declared status is a free third authority and is recorded
# verbatim -- including `unknown`, which is not the same as absent.
set -u
LIST="$1"; OUT="$2"; PIN="$3"; BUDGET="${4:-60}"
CORPUS="${5:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
Z3="${CS_Z3:-z3}"
command -v "$Z3" >/dev/null || { echo "ABORT: $Z3 not found"; exit 2; }

printf 'file\tz3\trc\tms\tdeclared\thost\tcore\n' > "$OUT"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  t0=$(date +%s%N)
  raw=$(taskset -c "$PIN" timeout $((BUDGET + 60)) "$Z3" "-T:$BUDGET" "$CORPUS/$f" 2>/dev/null)
  rc=$?
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
  d=$(grep -m1 -oE ':status[[:space:]]+[a-z]+' "$CORPUS/$f" | awk '{print $2}' || true)
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$f" "${v:-NOVERDICT}" "$rc" "$(( (t1 - t0) / 1000000 ))" "${d:-ABSENT}" \
    "$(hostname)" "$PIN" >> "$OUT"
done < "$LIST"
echo "DONE $OUT"
