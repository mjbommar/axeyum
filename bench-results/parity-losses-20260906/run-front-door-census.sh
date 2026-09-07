#!/usr/bin/env bash
set -u
BIN="$HOME/uf-census-snap/target/release/examples/uf_unknown_probe"
LIST="$1"
OUT="$2"
BUDGET_MS="${3:-24000}"
mkdir -p "$OUT"
n=0
while IFS= read -r f; do
  n=$((n+1))
  [ -z "$f" ] && continue
  start=$(date +%s%N)
  taskset -c 0-7 timeout -k 5 120 env AXEYUM_QTRACE=1 "$BIN" "$f" "$BUDGET_MS" \
    > "$OUT/$n.out" 2> "$OUT/$n.err"
  rc=$?
  end=$(date +%s%N)
  wall=$(( (end - start) / 1000000 ))
  printf 'path\t%s\nwall_ms\t%s\nexit\t%s\n' "$f" "$wall" "$rc" > "$OUT/$n.meta"
  echo "[$n] rc=$rc wall=${wall}ms $(head -1 "$OUT/$n.out")"
done < "$LIST"
echo "ALLDONE $n files"
