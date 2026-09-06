#!/usr/bin/env bash
# Front-door (`solve_smtlib`) probe with qtrace, one file per line on stdin.
set -u
BIN=./target/release/examples/uf_unknown_probe
TO=${2:-24000}
while read -r f; do
  [ -z "$f" ] && continue
  echo "=== $(basename "$f")"
  start=$(date +%s%N)
  AXEYUM_QTRACE=1 timeout 60 taskset -c 0-7 "$BIN" "$f" "$TO" 2>&1 | head -30
  end=$(date +%s%N)
  echo "    wall_ms=$(( (end-start)/1000000 ))"
done < "$1"
