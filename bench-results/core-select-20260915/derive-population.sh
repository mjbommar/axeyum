#!/usr/bin/env bash
export LC_ALL=C
# CORE-SELECT -- derive every list this lane uses BY SCRIPT from committed
# artifacts.  A typed list is a measurement of the maintainer's memory.
#
# The AUTHORITY for "which 200 files" is `bench-results/parity-lists/<D>.txt`
# (the pinned per-division lists).  The tier-1 board TSVs are used ONLY for the
# INHERITED verdict, which this lane re-derives before counting anything
# (ADR-2035 found 8 of 22 censused rows were decided anyway).
#
# Every derivation carries a POSITIVE CONTROL: the complementary filter over
# the same column of the same file must be non-empty, so an empty result is a
# finding about the population and not about the filter.
set -eu
W="$(cd "$(dirname "$0")" && pwd)"
PL="$W/../parity-lists"
T1="$W/../tier1-current-20260914"
CORPUS="${CS_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
DIVS="UFNIA QF_NIA UFLIA AUFDTLIRA UFDTLIRA AUFLIRA UF"
mkdir -p "$W/lists"

: > "$W/lists/tier1-all.list"
: > "$W/lists/inherited-undecided.list"
for d in $DIVS; do
  [ -r "$PL/$d.txt" ] || { echo "ABORT: $PL/$d.txt missing"; exit 2; }
  # AUFLIRA's board was re-measured post-merge at 787bbefee (ADR-2065's +14);
  # use that snapshot where it exists, so the INHERITED number is the freshest
  # committed one rather than the one this lane would most like to inherit.
  tsv="$T1/$d.tsv"
  [ -r "$T1/$d-postmerge-787bbefee.tsv" ] && tsv="$T1/$d-postmerge-787bbefee.tsv"
  [ -r "$tsv" ] || { echo "ABORT: $tsv missing"; exit 2; }

  sed "s#^$CORPUS/##" "$PL/$d.txt" | awk 'NF' >> "$W/lists/tier1-all.list"
  u=$(awk -F'\t' 'NR>1 && $2=="unknown"{print $1}' "$tsv" | sort -u | tee -a "$W/lists/inherited-undecided.list" | wc -l)
  k=$(awk -F'\t' 'NR>1 && ($2=="sat"||$2=="unsat"){print $1}' "$tsv" | sort -u | wc -l)
  [ "$u" -gt 0 ] || { echo "ABORT: $d has no undecided rows -- column 2 is not the one we think"; exit 3; }
  [ "$k" -gt 0 ] || { echo "ABORT: $d has no decided rows -- column 2 is not the one we think"; exit 3; }
  printf '%-10s pinned=%s inherited undecided=%s decided=%s  (%s)\n' \
    "$d" "$(grep -c . "$PL/$d.txt")" "$u" "$k" "$(basename "$tsv")"
done
sort -u -o "$W/lists/tier1-all.list" "$W/lists/tier1-all.list"
sort -u -o "$W/lists/inherited-undecided.list" "$W/lists/inherited-undecided.list"

echo "tier1-all:            $(grep -c . "$W/lists/tier1-all.list")"
echo "inherited-undecided:  $(grep -c . "$W/lists/inherited-undecided.list")"

# The PINNED lists are the authority for "which files"; the board TSVs supply
# only the inherited verdict.  Where the two disagree about membership, print
# the rows -- a silent join would drop them.  Measured 2026-09-15: exactly ONE
# row drifts (`QF_NIA/20170427-VeryMax/SAT14/106.smt2` on the board where the
# pinned list has `QF_NIA/mcm/106.smt2`; BOTH files exist in the corpus, so
# this is a basename collision in the board's runner, not a missing file).
comm -23 "$W/lists/inherited-undecided.list" "$W/lists/tier1-all.list" > "$W/lists/board-only.list"
miss=$(grep -c . "$W/lists/board-only.list" || true)
echo "board rows NOT in the pinned lists (population is the PINNED list): $miss"
[ "$miss" -eq 0 ] || sed 's/^/  board-only: /' "$W/lists/board-only.list"

# And every pinned file must exist and be non-empty on disk: a census over
# files still being written reports a false absence (ADR-2080).
absent=0; empty=0
while IFS= read -r f; do
  if [ ! -f "$CORPUS/$f" ]; then absent=$((absent + 1))
  elif [ ! -s "$CORPUS/$f" ]; then empty=$((empty + 1)); fi
done < "$W/lists/tier1-all.list"
echo "corpus presence: absent=$absent empty=$empty of $(grep -c . "$W/lists/tier1-all.list")"
[ "$absent" -eq 0 ] && [ "$empty" -eq 0 ] || { echo "ABORT: corpus incomplete"; exit 5; }
