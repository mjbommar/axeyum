#!/usr/bin/env bash
# Interleaved per-file A/B of the `AXEYUM_NRA_CAD` arms (ADR-2121).
#
# ONE binary, TWO env values. Both arms run back to back on the SAME file on the
# SAME pinned core, and the order alternates with the file index so neither arm
# systematically gets the cold cache. That is ADR-2110's protocol, and the reason
# for it is measured: the same binary scored 77, 79 and 85 on one division in a
# single day purely on ambient load, so only the DIFFERENCE survives contention.
#
# Arms here:
#   A = `default`     -- the env var SET and EMPTY. `CadPolicy::DEFAULT`, with
#                        `single_cell: false`, which is one bool test away from
#                        the pre-ADR-2121 engine.
#   B = `single-cell` -- ADR-2121's route, with the SAME `cell_cap` as `default`
#                        so the difference is the ROUTE and not the budget.
#
# The arm B value is a parameter (`--arm-b`) rather than a constant, because the
# same runner has to serve the QF_LRA control, where the expected answer is that
# nothing moves at all.
#
# Exit status: non-zero unless BOTH arms produced a verdict token for every file.
set -u

LIST=""; OUT=""; SHARD=""; CORE=""; BIN=""; ARM_B="single-cell"
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
    --corpus-root) CORPUS_ROOT="$2"; shift 2 ;;
    --budget-s) BUDGET_S="$2"; shift 2 ;;
    *) echo "ab-run: unknown argument $1" >&2; exit 2 ;;
  esac
done
for required in LIST OUT SHARD CORE BIN; do
  if [ -z "${!required}" ]; then echo "ab-run: --${required,,} required" >&2; exit 2; fi
done

one_arm() {  # $1 env value, $2 corpus-relative path -> verdict token
  local raw
  raw="$(AXEYUM_NRA_CAD="$1" taskset -c "$CORE" timeout $((BUDGET_S + 6)) \
      bash -c "ulimit -v $VLIMIT_KB; exec '$BIN' '$CORPUS_ROOT/$2' --timeout-ms $((BUDGET_S * 1000))" \
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
    va="$(one_arm "" "$rel")"; t1=$(date +%s%N)
    vb="$(one_arm "$ARM_B" "$rel")"; t2=$(date +%s%N)
    ams=$(( (t1 - t0) / 1000000 )); bms=$(( (t2 - t1) / 1000000 ))
  else
    vb="$(one_arm "$ARM_B" "$rel")"; t1=$(date +%s%N)
    va="$(one_arm "" "$rel")"; t2=$(date +%s%N)
    bms=$(( (t1 - t0) / 1000000 )); ams=$(( (t2 - t1) / 1000000 ))
  fi
  [ "$va" = "none" ] && missing=$((missing + 1))
  [ "$vb" = "none" ] && missing=$((missing + 1))
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$rel" "$va" "$vb" "$ams" "$bms" "$first" >> "$OUT"
  echo "[ab$SHARD $n] A=$va B=$vb $rel" >&2
done < "$LIST"

echo "ab-run: shard$SHARD covered $n files, $missing arm-runs without a verdict token" >&2
[ "$missing" -eq 0 ]
