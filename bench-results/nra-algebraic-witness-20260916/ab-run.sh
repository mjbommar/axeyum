#!/usr/bin/env bash
# Interleaved per-file A/B (ADR-2110 protocol), extended by ADR-2134.
#
# ONE binary, TWO env values -- or, with `--binary-a`, TWO binaries and the same
# env value. Both arms run back to back on the SAME file on the SAME pinned
# core, and the order alternates with the file index so neither arm
# systematically gets the cold cache. The reason for the protocol is measured:
# the same binary scored 77, 79 and 85 on one division in a single day purely on
# ambient load, so only the DIFFERENCE survives contention.
#
# `--binary-a` exists because ADR-2134 has TWO things to price and they are not
# both env-selectable. The `algebraic-witness` ARM is an env value. The
# `RealAlgebraic::sign_at` exactness fix is NOT behind any lever -- a wrong sign
# in the trusted evaluator is not something to ship as an option -- so pricing it
# needs the old binary against the new one at the same arm.
#
# Arms here:
#   A = `--arm-a` (default: the env var SET and EMPTY, i.e. the shipped default)
#   B = `--arm-b`
#
# Exit status: non-zero unless BOTH arms produced a verdict token for every file.

set -u

LIST=""; OUT=""; SHARD=""; CORE=""; BIN=""; ARM_B="single-cell"; ARM_A=""
BIN_A=""
CORPUS_ROOT="/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental"
BUDGET_S=24
VLIMIT_KB=$((8 * 1024 * 1024))

while [ $# -gt 0 ]; do
  case "$1" in
    --list) LIST="$2"; shift 2 ;;
    --out) OUT="$2"; shift 2 ;;
    --shard) SHARD="$2"; shift 2 ;;
    --core) CORE="$2"; shift 2 ;;
    --binary) BIN="$2"; shift 2 ;;
    --arm-b) ARM_B="$2"; shift 2 ;;
    --arm-a) ARM_A="$2"; shift 2 ;;
    --binary-a) BIN_A="$2"; shift 2 ;;
    --corpus-root) CORPUS_ROOT="$2"; shift 2 ;;
    --budget-s) BUDGET_S="$2"; shift 2 ;;
    *) echo "ab-run: unknown argument $1" >&2; exit 2 ;;
  esac
done
for required in LIST OUT SHARD CORE BIN; do
  if [ -z "${!required}" ]; then echo "ab-run: --${required,,} required" >&2; exit 2; fi
done

one_arm() {  # $1 env value, $2 corpus-relative path, $3 binary -> verdict token
  local raw bin
  bin="${3:-$BIN}"
  raw="$(AXEYUM_NRA_CAD="$1" taskset -c "$CORE" timeout $((BUDGET_S + 6)) \
      bash -c "ulimit -v $VLIMIT_KB; exec '$bin' '$CORPUS_ROOT/$2' --timeout-ms $((BUDGET_S * 1000))" \
      2>/dev/null)" || true
  printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$' || printf 'none\n'
}

printf 'file\tA\tB\tA_ms\tB_ms\tfirst\n' > "$OUT"
n=0
missing=0
while IFS= read -r rel; do
  [ -n "$rel" ] || continue
  n=$((n + 1))
  if [ $(( n % 2 )) -eq 1 ]; then first="A"; else first="B"; fi
  t0=$(date +%s%N)
  if [ "$first" = "A" ]; then
    va="$(one_arm "$ARM_A" "$rel" "${BIN_A:-$BIN}")"; t1=$(date +%s%N)
    vb="$(one_arm "$ARM_B" "$rel" "$BIN")"; t2=$(date +%s%N)
    ams=$(( (t1 - t0) / 1000000 )); bms=$(( (t2 - t1) / 1000000 ))
  else
    vb="$(one_arm "$ARM_B" "$rel" "$BIN")"; t1=$(date +%s%N)
    va="$(one_arm "$ARM_A" "$rel" "${BIN_A:-$BIN}")"; t2=$(date +%s%N)
    bms=$(( (t1 - t0) / 1000000 )); ams=$(( (t2 - t1) / 1000000 ))
  fi
  [ "$va" = "none" ] && missing=$((missing + 1))
  [ "$vb" = "none" ] && missing=$((missing + 1))
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$rel" "$va" "$vb" "$ams" "$bms" "$first" >> "$OUT"
  echo "[ab$SHARD $n] A=$va B=$vb $rel" >&2
done < "$LIST"

echo "ab-run: shard$SHARD covered $n files, $missing arm-runs without a verdict token" >&2
[ "$missing" -eq 0 ]
