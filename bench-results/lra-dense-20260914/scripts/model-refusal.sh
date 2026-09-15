#!/usr/bin/env bash
# R12: what IS the online engine's refusal?
#
# ADR-2045 named the capability wall as one sentence -- "online CDCL(T) LRA model
# did not replay (arithmetic outside the incremental engine)" -- carried by 19 of
# 21 rows that reach the engine, and handed it off as the work.
#
# That sentence covers TWO structurally different failures at its two call sites
# in `lra_theory.rs`, and the first splits five further ways inside
# `lra_online::model`:
#
#   lra_theory:no-model-reconstructed        the engine produced no point at all
#     sync-failed                              bounds could not be synced
#     live-system-infeasible                   the live system is UNSAT now
#     simplex-declined                         overflow / pivot cap / deadline
#     feasible-but-witness-out-of-i128         FEASIBLE and we decline anyway
#     fm-fallback-declined                     the FM fallback gave up
#   lra_theory:model-built-but-does-not-replay  a model WAS built and does not
#                                               satisfy the original assertions
#
# These demand opposite work. The last of the five is the one worth separating
# most: it is a query that HAS a model, declined because `Incremental::point`
# narrows to `i128` and drops the whole vector if one coordinate does not fit --
# already tracked as roadmap item 2.3. If that arm dominates, the "capability
# wall" is a known open item and not new work.
#
# Usage: model-refusal.sh <list> <bin> [budget_s]
set -u
LIST="$1"; BIN="$2"; BUDGET="${3:-24}"
VLIM=$((8 * 1024 * 1024))
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT

: > "$T/all"
rows=0
while read -r f; do
  [ -z "$f" ] && continue
  rows=$((rows + 1))
  ( ulimit -v $VLIM
    env AXEYUM_LRAMODELPROBE=1 timeout $((BUDGET + 16)) "$BIN" "$f" \
      --timeout-ms $((BUDGET * 1000))
  ) > "$T/out" 2> "$T/err"
  n=$(grep -c LRAMODELPROBE "$T/err")
  printf '%-5s %-7s %s\n' "$n" \
    "$(grep -m1 -oE '^(sat|unsat|unknown)$' "$T/out" || echo none)" \
    "$(basename "$f" | cut -c1-56)"
  # `[a-z:-]` would truncate `lra_theory:...` at the underscore and print
  # `site=lra`, which reads as a site that does not exist. The class must carry
  # `_` and digits.
  grep -oE 'site=[A-Za-z0-9_:-]+' "$T/err" | sort -u | sed "s|\$| $(basename "$f")|" >> "$T/rows"
  grep -oE 'site=[A-Za-z0-9_:-]+' "$T/err" >> "$T/all"
done < "$LIST"

echo
echo "== rows=$rows =="
echo "== which refusal, by OCCURRENCE =="
sort "$T/all" | uniq -c | sort -rn
echo "== which refusal, by ROW (a row that looped 400 times counts once) =="
# Occurrence counts are dominated by whichever row looped most, so the ROW count
# is the one that sizes the work.
awk '{print $1}' "$T/rows" | sort | uniq -c | sort -rn
