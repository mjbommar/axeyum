#!/usr/bin/env bash
# S11a interleaved before/after arm.
#
# Runs BOTH binaries on each file back to back, so the two arms see the same
# machine load — the load skew between two sequential whole-list runs is the
# thing that invalidates a wall-clock comparison on a multi-lane box.
#
# usage: run-interleaved.sh <list.txt> <before.tsv> <after.tsv> <before_bin> <after_bin> [timeout_ms]
set -u
LIST=$1; OUTB=$2; OUTA=$3; BINB=$4; BINA=$5; TO=${6:-24000}

emit() {  # emit <outfile> <file> <raw> <wall_ms>
  local v
  case "$3" in
    sat*)     v=sat ;;
    unsat*)   v=unsat ;;
    unknown*) v=unknown ;;
    error*)   v=error ;;
    *)        v=no-output ;;
  esac
  printf '%s\t%s\t%s\t%s\n' "$2" "$v" "$4" "${3:0:400}" >> "$1"
}

printf 'file\tverdict\twall_ms\tdetail\n' > "$OUTB"
printf 'file\tverdict\twall_ms\tdetail\n' > "$OUTA"

n=0
while read -r f; do
  [ -z "$f" ] && continue
  n=$((n+1))

  s=$(date +%s%N)
  raw=$(timeout 120 taskset -c 0-7 "$BINB" "$f" "$TO" 2>/dev/null | tr '\n' ' ')
  e=$(date +%s%N)
  emit "$OUTB" "$f" "$raw" "$(( (e-s)/1000000 ))"

  s=$(date +%s%N)
  raw=$(timeout 120 taskset -c 0-7 "$BINA" "$f" "$TO" 2>/dev/null | tr '\n' ' ')
  e=$(date +%s%N)
  emit "$OUTA" "$f" "$raw" "$(( (e-s)/1000000 ))"

  if [ $((n % 12)) -eq 0 ]; then
    echo "  ... $n files" >&2
  fi
done < "$LIST"
echo "done: $n files" >&2
