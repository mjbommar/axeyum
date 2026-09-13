#!/usr/bin/env bash
# Run `array_real_gate_census` over WHOLE divisions and write one TSV per
# division plus a combined summary.
#
# The divisions are every SMT-LIB division whose logic string can carry BOTH an
# array and a Real, plus the two array divisions that carry NO Real (ALIA,
# QF_ALIA) as the negative control: a census that only looks where it expects a
# hit cannot tell a real population from a classifier bug, and `real_gate_only`
# must be exactly 0 in the control divisions.
#
# Usage: census.sh <census-binary> <out-dir>
set -eu
BIN="${1:?usage: census.sh <census-binary> <out-dir>}"
OUT="${2:?usage: census.sh <census-binary> <out-dir>}"
ROOT=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental

# Real-carrying array divisions, then the no-Real array controls.
DIVISIONS="AUFLIRA AUFNIRA AUFDTLIRA AUFDTNIRA AUFFPDTNIRA ABVFPLRA QF_ABVFPLRA ALIA QF_ALIA"

mkdir -p "$OUT"
for d in $DIVISIONS; do
  [ -d "$ROOT/$d" ] || { echo "SKIP $d (absent)"; continue; }
  find "$ROOT/$d" -name '*.smt2' | sort > "$OUT/$d.list"
  n=$(wc -l < "$OUT/$d.list")
  [ "$n" -gt 0 ] || { echo "ABORT: $d list is empty"; exit 2; }
  echo "== $d ($n files)"
  "$BIN" "$OUT/$d.list" > "$OUT/$d.files.tsv" 2> "$OUT/$d.summary.txt"
  cat "$OUT/$d.summary.txt"
done
