#!/usr/bin/env bash
# SILENT-HANG -- derive the population from the COMMITTED census rather than
# typing it.  A typed list is a measurement of the maintainer's memory.
#
# The bucket is: undecided, no route line at all, and the give-up kind is
# `Watchdog`.  All three conditions are required -- `bound_by=NONE` alone also
# matches a row that produced no trail for some other reason, and the point of
# this lane is that a label can cover more than one cause.
set -eu
W="$(cd "$(dirname "$0")" && pwd)"
SRC="$W/../skeleton-reach-20260914/ref/fd-census-208.tsv"
[ -r "$SRC" ] || { echo "ABORT: census $SRC missing"; exit 2; }
mkdir -p "$W/lists"

# POSITIVE CONTROL ON THE DERIVATION ITSELF (R2): the same awk, same columns,
# asking for the complement.  If this prints 0 the filter is matching nothing
# for a reason that has nothing to do with the bucket.
comp=$(awk -F'\t' '$2=="unknown" && $3!="NONE"' "$SRC" | wc -l)
[ "$comp" -gt 0 ] || { echo "ABORT: complement is empty -- the filter is broken, not the bucket"; exit 3; }
echo "derivation control: $comp undecided rows DO carry a bound_by -- the columns are the ones we think they are"

awk -F'\t' '$2=="unknown" && $3=="NONE" && $7=="Watchdog"{print $1}' "$SRC" \
  | sort > "$W/lists/population-13.list"

n=$(wc -l < "$W/lists/population-13.list")
echo "population: $n rows -> $W/lists/population-13.list"
awk -F/ '{print $1}' "$W/lists/population-13.list" | sort | uniq -c

# The POSITIVE-CONTROL population for the instrument check: rows that are also
# undecided but DO carry a route line, drawn from the same census and the same
# division, so the only difference is the thing under test.
awk -F'\t' '$2=="unknown" && $3!="NONE" && $1 ~ /^UFNIA\//{print $1"\t"$3}' "$SRC" \
  | sort > "$W/lists/control-has-route.tsv"
echo "control (has a route line): $(wc -l < "$W/lists/control-has-route.tsv") UFNIA rows"
