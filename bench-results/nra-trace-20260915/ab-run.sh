#!/usr/bin/env bash
# Interleaved per-file A/B of the `AXEYUM_NRA_CAD` arms (ADR-2110, NRA-TRACE).
#
# ONE binary, TWO env values. Both arms run back to back on the SAME file on the
# SAME pinned core, and the order alternates with the file index so neither arm
# systematically gets the cold cache. That is the protocol
# `bench-results/board-ab-20260915/README.md` settled on, and the reason for it
# is measured: the same binary scored 77, 79 and 85 on one division in a single
# day purely on ambient load, so only the DIFFERENCE survives contention.
#
# Arms:
#   A = `default` -- the env var unset. Byte-identical to the pre-ADR-2110
#       engine: `CadPolicy::DEFAULT.cell_cap` IS `MAX_CAD_CELLS`.
#   B = `wide`    -- 16x the cell cap.
#
# Every run goes through `scripts/ledger-run-one.sh`, so both arms land as
# outcome-ledger rows with their own `arm` column and the captures are kept.
#
# Usage:
#   ab-run.sh --root DIR --list FILE --outdir DIR --shard N --core 1,9 \
#             --sweep-id ID --binary PATH --binary-sha SHA [--corpus-root DIR]
#
# Exit status: non-zero unless BOTH arms produced a ledger row for every file.
set -u

ROOT=""; LIST=""; OUT=""; SHARD=""; CORE=""; SWEEP_ID=""; BIN=""; BIN_SHA=""
CORPUS_ROOT="/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental"
BUDGET_S=24
VLIMIT_KB=$((8 * 1024 * 1024))

while [ $# -gt 0 ]; do
  case "$1" in
    --root) ROOT="$2"; shift 2 ;;
    --list) LIST="$2"; shift 2 ;;
    --outdir) OUT="$2"; shift 2 ;;
    --shard) SHARD="$2"; shift 2 ;;
    --core) CORE="$2"; shift 2 ;;
    --sweep-id) SWEEP_ID="$2"; shift 2 ;;
    --binary) BIN="$2"; shift 2 ;;
    --binary-sha) BIN_SHA="$2"; shift 2 ;;
    --corpus-root) CORPUS_ROOT="$2"; shift 2 ;;
    --budget-s) BUDGET_S="$2"; shift 2 ;;
    *) echo "ab-run: unknown argument $1" >&2; exit 2 ;;
  esac
done
for required in ROOT LIST OUT SHARD CORE SWEEP_ID BIN BIN_SHA; do
  if [ -z "${!required}" ]; then
    echo "ab-run: --${required,,} is required" >&2; exit 2
  fi
done

LEDGER_DIR="$OUT/ledger-shard$SHARD"
LOGS="$OUT/logs"
mkdir -p "$LEDGER_DIR" "$LOGS" || exit 2
INDEX="$OUT/ab-shard$SHARD.tsv"
printf 'file\tA\tB\tA_ms\tB_ms\tfirst\n' > "$INDEX"

one_arm() {  # $1 arm name, $2 env value ("" = unset), $3 corpus-relative path
  local arm="$1" env_value="$2" rel="$3" line
  if [ -z "$env_value" ]; then
    line="$(AXEYUM_NRA_CAD= "$ROOT/scripts/ledger-run-one.sh" \
        --sweep-id "$SWEEP_ID" --arm "$arm" --binary "$BIN" \
        --binary-sha "$BIN_SHA" --file "$CORPUS_ROOT/$rel" \
        --corpus-root "$CORPUS_ROOT" --outdir "$LOGS" --budget-s "$BUDGET_S" \
        --vlimit-kb "$VLIMIT_KB" --core "$CORE" --ledger-dir "$LEDGER_DIR" \
        --note "nra-trace A/B arm=$arm shard$SHARD")"
  else
    line="$(AXEYUM_NRA_CAD="$env_value" "$ROOT/scripts/ledger-run-one.sh" \
        --sweep-id "$SWEEP_ID" --arm "$arm" --binary "$BIN" \
        --binary-sha "$BIN_SHA" --file "$CORPUS_ROOT/$rel" \
        --corpus-root "$CORPUS_ROOT" --outdir "$LOGS" --budget-s "$BUDGET_S" \
        --vlimit-kb "$VLIMIT_KB" --core "$CORE" --ledger-dir "$LEDGER_DIR" \
        --note "nra-trace A/B arm=$arm shard$SHARD")"
  fi
  local rc=$?
  if [ "$rc" -ne 0 ]; then printf 'ROWFAIL'; return 1; fi
  printf '%s\n' "$line" | awk -F'\t' '$1=="LEDGER-ROW"{print $5}'
}

failures=0
n=0
while IFS= read -r rel; do
  [ -n "$rel" ] || continue
  n=$((n + 1))
  slug="$(printf '%s' "$rel" | tr '/' '_')"
  if [ $(( n % 2 )) -eq 1 ]; then first="A"; else first="B"; fi

  t0=$(date +%s%N)
  if [ "$first" = "A" ]; then
    va="$(one_arm A "" "$rel")" || failures=$((failures + 1))
    t1=$(date +%s%N)
    vb="$(one_arm B wide "$rel")" || failures=$((failures + 1))
    t2=$(date +%s%N)
    ams=$(( (t1 - t0) / 1000000 )); bms=$(( (t2 - t1) / 1000000 ))
  else
    vb="$(one_arm B wide "$rel")" || failures=$((failures + 1))
    t1=$(date +%s%N)
    va="$(one_arm A "" "$rel")" || failures=$((failures + 1))
    t2=$(date +%s%N)
    bms=$(( (t1 - t0) / 1000000 )); ams=$(( (t2 - t1) / 1000000 ))
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$rel" "${va:-none}" "${vb:-none}" "$ams" "$bms" "$first" >> "$INDEX"
  echo "[ab$SHARD $n] A=${va:-none} B=${vb:-none} $slug"
done < "$LIST"

echo "ab-run: shard$SHARD covered $n files, $failures missing rows" >&2
[ "$failures" -eq 0 ]
