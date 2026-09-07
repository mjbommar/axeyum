#!/usr/bin/env bash
# Interleaved arms: every arm sees each file back to back, so all arms share the
# same machine load.  Arm spec is "name:ENV1=1,ENV2=1" (empty env = baseline).
set -u
BIN="$HOME/uf-census-snap/target/release/examples/uf_unknown_probe"
LIST="$1"
OUT="$2"
BUDGET_MS="${3:-24000}"
shift 3
mkdir -p "$OUT"
n=0
while IFS= read -r f; do
  n=$((n + 1))
  [ -z "$f" ] && continue
  for spec in "$@"; do
    arm="${spec%%:*}"
    envs="${spec#*:}"
    envargs=()
    if [ -n "$envs" ] && [ "$envs" != "$arm" ]; then
      IFS=',' read -ra parts <<<"$envs"
      for p in "${parts[@]}"; do envargs+=("$p"); done
    fi
    start=$(date +%s%N)
    taskset -c 0-7 timeout -k 5 120 env AXEYUM_QTRACE=1 "${envargs[@]}" "$BIN" "$f" "$BUDGET_MS" \
      >"$OUT/$arm.$n.out" 2>"$OUT/$arm.$n.err"
    rc=$?
    end=$(date +%s%N)
    wall=$(((end - start) / 1000000))
    printf 'path\t%s\nwall_ms\t%s\nexit\t%s\n' "$f" "$wall" "$rc" >"$OUT/$arm.$n.meta"
    echo "[$n/$arm] rc=$rc wall=${wall}ms $(head -1 "$OUT/$arm.$n.out")"
  done
done <"$LIST"
echo "ALLDONE $n files"
