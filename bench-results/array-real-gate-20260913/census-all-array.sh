#!/usr/bin/env bash
# The census over EVERY array-carrying SMT-LIB division, not only the ones whose
# logic NAME contains an R.
#
# Why the wider sweep exists: the targeted run (`census.sh`) found zero
# `real_gate_only` files in the divisions ADR-1955 named, and "we looked where
# we expected a hit and found none" is not a denominator. A benchmark may
# declare a stronger logic than it uses (`ALL`, or an `AUF…` name over a file
# that also carries a Real), so the population this change reaches can only be
# bounded by asking the parser about every division that can hold an array at
# all. An empty result from an instrument never pointed at the subject is
# indistinguishable from a strong negative.
#
# Usage: census-all-array.sh <census-binary> <out-dir> [taskset-cores]
set -eu
BIN="${1:?usage: census-all-array.sh <census-binary> <out-dir> [cores]}"
OUT="${2:?usage: census-all-array.sh <census-binary> <out-dir> [cores]}"
CORES="${3:-}"
ROOT=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental

# Every division whose logic can contain an array (the `A` in the logic name),
# including the ones already covered by census.sh so this run stands alone.
DIVISIONS="ABV ABVFP ABVFPLRA ALIA ANIA AUFBV AUFBVDTLIA AUFBVDTNIA \
AUFBVDTNIRA AUFBVFP AUFDTLIA AUFDTLIRA AUFDTNIRA AUFFPDTNIRA AUFLIA AUFLIRA \
AUFNIA AUFNIRA QF_ABV QF_ABVFP QF_ABVFPLRA QF_ALIA QF_ANIA QF_AUFBV \
QF_AUFBVFP QF_AUFLIA QF_AUFNIA QF_AX"

RUN=""
[ -n "$CORES" ] && RUN="taskset -c $CORES"

mkdir -p "$OUT"
for d in $DIVISIONS; do
  [ -d "$ROOT/$d" ] || { echo "SKIP $d (absent)"; continue; }
  find "$ROOT/$d" -name '*.smt2' | sort > "$OUT/$d.list"
  n=$(wc -l < "$OUT/$d.list")
  [ "$n" -gt 0 ] || { echo "ABORT: $d list is empty"; exit 2; }
  echo "== $d ($n files)"
  # shellcheck disable=SC2086
  $RUN "$BIN" "$OUT/$d.list" > "$OUT/$d.files.tsv" 2> "$OUT/$d.summary.txt"
  cat "$OUT/$d.summary.txt"
done
echo "CENSUS-ALL-DONE"
