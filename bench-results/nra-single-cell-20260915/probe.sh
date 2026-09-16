#!/usr/bin/env bash
# A capability PROBE, not the A/B: run one list through ONE binary under two
# `AXEYUM_NRA_CAD` values and print the verdict pair per file.
#
# This exists to answer "does the route fire at all, and on what" before an
# interleaved A/B is worth its wall clock. It does NOT control for load and its
# timings must not be quoted -- the A/B runner does that. The verdicts are still
# comparable because the two arms are the same binary on the same file.
#
# Usage: probe.sh --binary PATH --list FILE --out TSV [--arm-b single-cell]
#                 [--core N] [--budget-s N] [--corpus-root DIR]
set -u

BIN=""; LIST=""; OUT=""; ARM_B="single-cell"; CORE=""; BUDGET_S=24
CORPUS_ROOT="/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental"
VLIMIT_KB=$((8 * 1024 * 1024))

while [ $# -gt 0 ]; do
  case "$1" in
    --binary) BIN="$2"; shift 2 ;;
    --list) LIST="$2"; shift 2 ;;
    --out) OUT="$2"; shift 2 ;;
    --arm-b) ARM_B="$2"; shift 2 ;;
    --core) CORE="$2"; shift 2 ;;
    --budget-s) BUDGET_S="$2"; shift 2 ;;
    --corpus-root) CORPUS_ROOT="$2"; shift 2 ;;
    *) echo "probe: unknown argument $1" >&2; exit 2 ;;
  esac
done
for required in BIN LIST OUT; do
  if [ -z "${!required}" ]; then echo "probe: --${required,,} required" >&2; exit 2; fi
done

run_one() {  # $1 env value, $2 corpus-relative path -> verdict token on stdout
  local env_value="$1" rel="$2" raw pinned=()
  [ -n "$CORE" ] && pinned=(taskset -c "$CORE")
  raw="$(AXEYUM_NRA_CAD="$env_value" "${pinned[@]}" \
      timeout $((BUDGET_S + 6)) \
      bash -c "ulimit -v $VLIMIT_KB; exec '$BIN' '$CORPUS_ROOT/$2' --timeout-ms $((BUDGET_S * 1000))" \
      2>/dev/null)" || true
  printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$' || printf 'none\n'
}

printf 'file\tA_default\tB_%s\tA_ms\tB_ms\n' "$ARM_B" > "$OUT"
n=0
while IFS= read -r rel; do
  [ -n "$rel" ] || continue
  n=$((n + 1))
  t0=$(date +%s%N)
  va="$(run_one "" "$rel")"
  t1=$(date +%s%N)
  vb="$(run_one "$ARM_B" "$rel")"
  t2=$(date +%s%N)
  printf '%s\t%s\t%s\t%s\t%s\n' "$rel" "$va" "$vb" \
    $(( (t1 - t0) / 1000000 )) $(( (t2 - t1) / 1000000 )) >> "$OUT"
  echo "[probe $n] A=$va B=$vb $rel" >&2
done < "$LIST"
echo "probe: $n files -> $OUT" >&2
