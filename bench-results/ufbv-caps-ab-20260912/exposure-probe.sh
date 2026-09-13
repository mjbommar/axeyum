#!/usr/bin/env bash
# Does the route these caps govern even RUN on a population?
#
# A control population that never reaches the cap being raised cannot lose, so
# its "0 losses" would mean nothing. `decided_by`/`bound_by` cannot answer this:
# a route that declines in 1 ms is neither, and the final `give-up` line belongs
# to whatever route ran LAST.
#
# `--trace` prints a `route-trail` JSON naming EVERY attempted route with its
# outcome and reason. That is the authority, and this probe reads it.
#
# Baseline settings only -- the question is about reach, not about the raise.
#
# Usage: exposure-probe.sh <shard> <nshard> <list> <pin> <out.tsv>
set -u
BUDGET=24
HEADROOM=16
SHARD="$1"; NSHARD="$2"; LIST="$3"; PIN="$4"; OUT="$5"
AX=/nas3/data/axeyum/harness/ufbv-caps/bin/smtcomp_cli
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/
[ -x "$AX" ] || { echo "ABORT shard $SHARD: $AX missing"; exit 2; }

printf 'file\tonline_route_in_trail\tcap_text_anywhere\ttrail_routes\n' > "$OUT"
idx=-1
while read -r f; do
  idx=$((idx + 1))
  [ $((idx % NSHARD)) -eq "$SHARD" ] || continue
  raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          env -u AXEYUM_UFBV_MAX_THEORY_ATOMS -u AXEYUM_UFBV_MAX_INPUT_DAG_NODES \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>/dev/null)
  trail=$(printf '%s\n' "$raw" | grep -m1 -oE '"route":"[^"]+"' | head -0)
  routes=$(printf '%s\n' "$raw" | grep -oE '"route":"[^"]+"' | cut -d'"' -f4 | sort -u | paste -sd, -)
  online=no
  case "$routes" in *ufbv-online*|*aufbv-online*|*abv-online*) online=yes ;; esac
  cap=no
  case "$raw" in
    *"semantic atoms"*|*"dynamic theory atoms"*|*"DAG nodes"*) cap=yes ;;
  esac
  printf '%s\t%s\t%s\t%s\n' "${f#"$CORPUS"}" "$online" "$cap" "${routes:-none}" >> "$OUT"
done < "$LIST"
echo "PROBE-DONE shard $SHARD $(($(wc -l < "$OUT") - 1)) rows"
