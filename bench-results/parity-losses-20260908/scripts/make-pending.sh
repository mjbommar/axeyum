#!/usr/bin/env bash
# Build `pending/<DIV>.txt` -- the confirm pass's input -- from `sweep/<DIV>.tsv`.
# Usage: make-pending.sh <DIV>...
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
out="$here/../pending"
mkdir -p "$out"
for d in "$@"; do
  src="$here/../sweep/$d.tsv"
  if [ ! -s "$src" ]; then
    echo "make-pending: no sweep/$d.tsv" >&2
    exit 1
  fi
  awk -F'\t' 'NR > 1 && $3 == "unsolved" { print $1 }' "$src" > "$out/$d.txt"
  echo "$d $(wc -l < "$out/$d.txt") pending"
done
