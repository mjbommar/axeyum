#!/usr/bin/env bash
set -u
BIN=./target/release/examples/uf_unknown_probe
TO=${2:-24000}
while read -r f; do
  [ -z "$f" ] && continue
  start=$(date +%s%N)
  out=$(timeout 90 taskset -c 0-7 "$BIN" "$f" "$TO" 2>/dev/null | tr '\n' ' ')
  end=$(date +%s%N)
  printf '%s\t%s\t%s\n' "$(( (end-start)/1000000 ))" "$(basename "$f")" "${out:0:220}"
done < "$1"
