#!/usr/bin/env bash
# Prove both levers are LIVE by MECHANISM, not by verdict count.
#
# ADR-2045's rule: a silently-ignored flag prints the same number as a flag that
# is read, so a verdict count cannot tell them apart. Each lever here formats
# something FROM ITS OWN VALUE, so the output cannot be produced any other way:
#
#   AXEYUM_LRA_SPARSE_ROWS  ->  the probe's `sparse=` field is 0 or 1, and the
#                               resident set at `dense-rows-built` stops growing
#   AXEYUM_LRA_CELL_CAP     ->  a `site=cell-cap-declined` line exists or does not
#
# The probe itself is proved live first: it must print NOTHING when unset.
#
# Environment is set with `env` and NOT with a `${v:+VAR=$v}` command prefix.
# That prefix does not work and fails SILENTLY in the lever's favour: bash
# recognises assignment words BEFORE expansion, so an assignment produced BY an
# expansion is passed as an argument instead, the variable is never set, and the
# arm reads as "no line" -- which the first draft of this script reported as a
# dead lever when the lever was fine.
#
# Usage: lever-mechanism-probe.sh <small-file> <over-cap-file> <bin>
set -u
SMALL="$1"; BIG="$2"; BIN="$3"
B=24000

echo "== 0. the probe is off by default (it must print nothing) =="
n=$(timeout 90 "$BIN" "$SMALL" --timeout-ms $B 2>&1 >/dev/null | grep -c LRADENSEPROBE)
echo "   probe lines with AXEYUM_LRADENSEPROBE unset: $n   (must be 0)"

echo
echo "== 1. AXEYUM_LRA_SPARSE_ROWS: the row form is formatted FROM the value =="
echo "   file: $(basename "$SMALL")"
for v in UNSET 1; do
  if [ "$v" = UNSET ]; then
    out=$(env AXEYUM_LRADENSEPROBE=1 timeout 90 "$BIN" "$SMALL" --timeout-ms $B 2>&1 >/dev/null)
  else
    out=$(env AXEYUM_LRADENSEPROBE=1 AXEYUM_LRA_SPARSE_ROWS="$v" \
          timeout 90 "$BIN" "$SMALL" --timeout-ms $B 2>&1 >/dev/null)
  fi
  printf '   SPARSE_ROWS=%-5s  %s\n' "$v" "$(printf '%s' "$out" | grep -m1 'site=dense-rows-built')"
  printf '   %-20s %s\n' '' "$(printf '%s' "$out" | grep -m1 'site=tableau-built')"
done
echo '   ^ rss_kb at dense-rows-built is the round trip; at tableau-built it is the peak.'

echo
echo "== 2. AXEYUM_LRA_CELL_CAP: the decline line exists only when set =="
echo "   file: $(basename "$BIG")   (its tableau is OVER MAX_TABLEAU_CELLS)"
for v in UNSET 1; do
  if [ "$v" = UNSET ]; then
    out=$(env AXEYUM_LRADENSEPROBE=1 timeout 90 "$BIN" "$BIG" --timeout-ms $B 2>&1 >/dev/null)
  else
    out=$(env AXEYUM_LRADENSEPROBE=1 AXEYUM_LRA_CELL_CAP="$v" \
          timeout 90 "$BIN" "$BIG" --timeout-ms $B 2>&1 >/dev/null)
  fi
  c=$(printf '%s' "$out" | grep -c 'site=cell-cap-declined')
  printf '   CELL_CAP=%-5s  cell-cap-declined lines: %-3s  %s\n' "$v" "$c" \
    "$(printf '%s' "$out" | grep -m1 'site=cell-cap-declined')"
  printf '   %-18s %s\n' '' "$(printf '%s' "$out" | grep -m1 'site=feasible_within-entry')"
done

echo
echo "== 3. a value that is not exactly \"1\" must NOT enable a lever =="
for v in 0 true yes " 1 "; do
  s=$(env AXEYUM_LRADENSEPROBE=1 AXEYUM_LRA_SPARSE_ROWS="$v" \
      timeout 90 "$BIN" "$SMALL" --timeout-ms $B 2>&1 >/dev/null \
      | grep -m1 -oE 'sparse=[01]')
  printf '   SPARSE_ROWS=%-7s -> %s\n' "\"$v\"" "${s:-<no line>}"
done
