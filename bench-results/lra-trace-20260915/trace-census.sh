#!/usr/bin/env bash
# LRA-TRACE: run one shard of the QF_LRA undecided population under `--trace`
# and keep all four cause channels.
#
# # Why not `ledger-run-one.sh` alone
#
# `scripts/ledger-run-one.sh` is the right per-file runner and this calls it,
# but ADR-2045 measured that **the give-up string is only one of four channels**
# and that a census built on it loses the largest bucket outright: 40 of 93 rows
# abort with NO give-up line at all, printing only to stderr. `ledger-run-one.sh`
# sends stderr to `/dev/null` (its capture is stdout, deliberately, because the
# ledger's parser reads a verdict and a trail from stdout). So this wrapper takes
# stderr ITSELF, to its own file, before handing the same invocation to the
# ledger runner would have thrown it away.
#
# Concretely the four channels ADR-2045 names, and where each lands here:
#
#   give-up line   -> $OUTDIR/<slug>.out     (stdout, with the route trail)
#   verdict        -> $OUTDIR/<slug>.out     (stdout)
#   exit status    -> the TSV `rc` column
#   allocator/panic-> $OUTDIR/<slug>.err     (stderr -- the 40 aborts' ONLY channel)
#
# # The probes
#
# Two diagnostics that already exist in the tree are armed here because they are
# the two the census question turns on, and both are print-only (nothing branches
# on either):
#
#   AXEYUM_LRADENSEPROBE=1   the offline dense route's shape and RSS at four
#                            points (ADR-2055's instrument)
#   AXEYUM_LRAMODELPROBE=1   WHICH of the five ways online model reconstruction
#                            failed (lra_online.rs:84)
#
# Arming them is itself a perturbation of the thing being measured, so the
# caller can turn them off with PROBES=0 and the row records which it was.
#
# Usage: trace-census.sh <shard-id> <list> <out.tsv> <cores> <bin> [budget_s]
set -u
SHARD="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX="$5"; BUDGET="${6:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/
PROBES="${PROBES:-1}"

[ -x "$AX" ] || { echo "ABORT: $AX missing or not executable"; exit 2; }
[ -r "$LIST" ] || { echo "ABORT: $LIST unreadable"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT non-empty; refusing to overwrite"; exit 2; }

OUTDIR="$(dirname -- "$OUT")/captures-$SHARD"
mkdir -p "$OUTDIR" || exit 2

printf 'file\trc\tms\tverdict\tprobes\tcapture\n' > "$OUT"

while read -r rel; do
  [ -z "$rel" ] && continue
  f="$CORPUS$rel"
  if [ ! -r "$f" ]; then echo "UNREADABLE $rel" >&2; continue; fi
  slug="$(printf '%s' "$rel" | tr '/' '_')"
  t0=$(date +%s%N)
  if [ "$PROBES" = "1" ]; then
    AXEYUM_LRADENSEPROBE=1 AXEYUM_LRAMODELPROBE=1 \
      timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
      bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
      "$AX" "$f" > "$OUTDIR/$slug.out" 2> "$OUTDIR/$slug.err"
  else
    timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
      bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
      "$AX" "$f" > "$OUTDIR/$slug.out" 2> "$OUTDIR/$slug.err"
  fi
  rc=$?
  t1=$(date +%s%N)
  # `grep -m1 -oE` on the bare verdict line, the harness's own convention, kept
  # identical to every other sweep here so the column is comparable.
  v=$(grep -m1 -oE '^(sat|unsat|unknown)$' -- "$OUTDIR/$slug.out" 2>/dev/null || true)
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$rel" "$rc" "$(( (t1 - t0) / 1000000 ))" "${v:-none}" "$PROBES" "$OUTDIR/$slug.out" >> "$OUT"
done < "$LIST"

echo "SHARD-DONE $SHARD $(($(wc -l < "$OUT") - 1)) rows"
