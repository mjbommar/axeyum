#!/usr/bin/env bash
# One census shard: every file in LIST through `smtcomp_cli --trace` under the
# board envelope, one outcome-ledger row each (ADR-2110, lane NRA-TRACE).
#
# This is a thin loop around `scripts/ledger-run-one.sh` -- the envelope, the
# capture and the ledger row all belong to that script, and re-inlining any of
# them is the exact defect ADR-2102 exists to stop. What this adds is the two
# things a SHARD needs and a single run does not:
#
#   * a per-shard `--ledger-dir`, because two concurrent appends to one
#     `INDEX.tsv` over NFS are a read-then-append race, and
#   * an `index.tsv` + `<n>.log` view of the same captures, so the EXISTING
#     classifier (`scripts/nra-loss-classify.py`, written 2026-09-09 and
#     already reading route attribution through `route_trace_reader` rather
#     than through the prose) can be run over this population unmodified as an
#     independent second reader.
#
# Usage:
#   census-run.sh --root DIR --list FILE --outdir DIR --shard N \
#                 --core 1,9 --sweep-id ID --binary PATH --binary-sha SHA \
#                 [--corpus-root DIR] [--budget-s 24] [--vlimit-kb 8388608]
#
# Exit status: 0 only when EVERY file in the list produced a ledger row. A file
# whose row failed to append is named on stderr and makes this non-zero -- a
# shard that silently covered 80 of 83 is a measurement of the 80.
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
    --vlimit-kb) VLIMIT_KB="$2"; shift 2 ;;
    *) echo "census-run: unknown argument $1" >&2; exit 2 ;;
  esac
done

for required in ROOT LIST OUT SHARD CORE SWEEP_ID BIN BIN_SHA; do
  if [ -z "${!required}" ]; then
    echo "census-run: --${required,,} is required" >&2
    exit 2
  fi
done

LEDGER_DIR="$OUT/ledger-shard$SHARD"
LOGS="$OUT/logs"
mkdir -p "$LEDGER_DIR" "$LOGS" || exit 2

INDEX="$OUT/index-shard$SHARD.tsv"
printf 'index\tfile\tverdict\twall_ms\n' > "$INDEX"

failures=0
n=0
while IFS= read -r rel; do
  [ -n "$rel" ] || continue
  n=$((n + 1))
  abs="$CORPUS_ROOT/$rel"
  line="$("$ROOT/scripts/ledger-run-one.sh" \
      --sweep-id "$SWEEP_ID" \
      --arm "shard$SHARD" \
      --binary "$BIN" \
      --binary-sha "$BIN_SHA" \
      --file "$abs" \
      --corpus-root "$CORPUS_ROOT" \
      --outdir "$LOGS" \
      --budget-s "$BUDGET_S" \
      --vlimit-kb "$VLIMIT_KB" \
      --core "$CORE" \
      --ledger-dir "$LEDGER_DIR" \
      --note "nra-trace census shard$SHARD")"
  rc=$?
  if [ "$rc" -ne 0 ]; then
    echo "census-run: NO LEDGER ROW for $rel (ledger-run-one exit $rc)" >&2
    failures=$((failures + 1))
    continue
  fi
  # `LEDGER-ROW <sweep> <arm> <rel> <verdict> <exit>`
  verdict="$(printf '%s\n' "$line" | awk -F'\t' '$1=="LEDGER-ROW"{print $5}')"
  slug="$(printf '%s' "$rel" | tr '/' '_')"
  capture="$LOGS/shard${SHARD}__${slug}.out"
  ln -f "$capture" "$LOGS/s${SHARD}n${n}.log" 2>/dev/null \
    || cp -f "$capture" "$LOGS/s${SHARD}n${n}.log"
  printf 's%sn%s\t%s\t%s\t%s\n' "$SHARD" "$n" "$rel" "${verdict:-ABORTED}" "0" \
    >> "$INDEX"
  echo "[shard$SHARD $n] ${verdict:-ABORTED} $rel"
done < "$LIST"

echo "census-run: shard$SHARD covered $n files, $failures without a ledger row" >&2
[ "$failures" -eq 0 ]
