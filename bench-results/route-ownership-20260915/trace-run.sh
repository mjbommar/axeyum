#!/usr/bin/env bash
# Single-arm `--trace` sweep for the ADR-2100 SIZING measurement.
#
# Emits one TSV row per file: the corpus-relative PATH (never the basename --
# 370 of 3,200 basenames are ambiguous), the verdict, the `; route` summary
# line, and the full `; route-trail` JSON. The trail is what the sizing analysis
# reads: it needs the ORDERED list of attempts, not just `last=`.
#
# Same envelope as every board here: 24 s wall, 8 GiB `ulimit -v`, one pinned
# physical core pair. NOT an A/B -- a single arm cannot make a claim about a
# delta, and nothing in the sizing does.
#
# Usage: trace-run.sh <tag> <list> <out.tsv> <cores> <bin> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX="$5"; BUDGET="${6:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }

printf 'file\tverdict\trc\tms\troute\ttrail\n' > "$OUT"
n=0
while read -r f; do
  [ -z "$f" ] && continue
  n=$((n + 1))
  t0=$(date +%s%N)
  raw=$(AXEYUM_TRACE=1 timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>/dev/null)
  rc=$?
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  # ADR-2075's trap, and this script FELL INTO IT on its first run: the
  # watchdog-kill path prints `; partial route ` and `; partial route-trail `,
  # a DELIBERATE prefix, so a `^; route ` anchor silently drops every
  # watchdog-killed file. Measured here: 103 of 645 rows came back with no
  # route line at all and the cause was this anchor, not a missing trace.
  # `-E '^; (partial )?route '` is the whole fix.
  route=$(printf '%s\n' "$raw" | grep -m1 -E '^; (partial )?route ' | tr '\t' ' ')
  trail=$(printf '%s\n' "$raw" | grep -m1 -E '^; (partial )?route-trail ' | tr '\t' ' ')
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
    "${f#"$CORPUS"}" "${v:-none}" "$rc" "$(( (t1 - t0) / 1000000 ))" \
    "${route:-none}" "${trail:-none}" >> "$OUT"
done < "$LIST"
echo "TRACE-DONE $TAG $n files -> $OUT"
