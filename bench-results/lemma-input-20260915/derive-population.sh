#!/usr/bin/env bash
# LEMMA-INPUT -- derive every list this lane uses BY SCRIPT from committed
# artifacts (R1).  A typed list is a measurement of the maintainer's memory.
#
# Each derivation carries a POSITIVE CONTROL: the complementary filter over the
# same columns of the same file must be non-empty, so an empty result is a
# finding about the population rather than about the filter.
set -eu
W="$(cd "$(dirname "$0")" && pwd)"
CENSUS="$W/../skeleton-reach-20260914/ref/fd-census-208.tsv"
SH="$W/../silent-hang-20260915/lists"
[ -r "$CENSUS" ] || { echo "ABORT: census $CENSUS missing"; exit 2; }
[ -r "$SH/still-9.list" ] || { echo "ABORT: $SH/still-9.list missing"; exit 2; }
mkdir -p "$W/lists"

# 1. The inherited 9, copied by path from ADR-2075's own derived list.
cp "$SH/still-9.list" "$W/lists/inherited-9.list"
echo "inherited (ADR-2075 bucket): $(grep -c . "$W/lists/inherited-9.list")"

# 2. EVERY row of the census, so the profile population is not restricted to
#    the bucket the previous lane happened to look at (the brief's item 1).
awk -F'\t' 'NF{print $1}' "$CENSUS" | sort -u > "$W/lists/census-all.list"
echo "census (all rows): $(grep -c . "$W/lists/census-all.list")"

# 3. The undecided half and the decided half, each with the other as its own
#    positive control.
awk -F'\t' '$2=="unknown"{print $1}' "$CENSUS" | sort -u > "$W/lists/census-undecided.list"
awk -F'\t' '$2=="sat"||$2=="unsat"{print $1}' "$CENSUS" | sort -u > "$W/lists/census-decided.list"
u=$(grep -c . "$W/lists/census-undecided.list")
d=$(grep -c . "$W/lists/census-decided.list")
[ "$u" -gt 0 ] || { echo "ABORT: no undecided rows -- the filter is broken"; exit 3; }
[ "$d" -gt 0 ] || { echo "ABORT: no decided rows -- the filter is broken"; exit 3; }
echo "derivation control: undecided=$u decided=$d (both non-empty, so column 2 is the one we think it is)"

awk -F/ 'NF{print $1}' "$W/lists/census-all.list" | sort | uniq -c
