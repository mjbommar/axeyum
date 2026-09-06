#!/usr/bin/env bash
# S11a measurement runner: front-door (`solve_smtlib`) verdict + wall per file.
# usage: run-arm.sh <list.txt> <out.tsv> <binary> [timeout_ms]
# Emits: file<TAB>verdict<TAB>wall_ms<TAB>detail
set -u
LIST=$1; OUT=$2; BIN=$3; TO=${4:-24000}
printf 'file\tverdict\twall_ms\tdetail\n' > "$OUT"
while read -r f; do
  [ -z "$f" ] && continue
  start=$(date +%s%N)
  raw=$(timeout 90 taskset -c 0-7 "$BIN" "$f" "$TO" 2>/dev/null | tr '\n' ' ')
  end=$(date +%s%N)
  ms=$(( (end-start)/1000000 ))
  case "$raw" in
    sat*)     v=sat ;;
    unsat*)   v=unsat ;;
    unknown*) v=unknown ;;
    error*)   v=error ;;
    *)        v=no-output ;;
  esac
  printf '%s\t%s\t%s\t%s\n' "$f" "$v" "$ms" "${raw:0:400}" >> "$OUT"
done < "$LIST"
