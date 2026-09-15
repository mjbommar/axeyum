#!/usr/bin/env bash
# LEMMA-INPUT -- the MECHANISM, read rather than argued: the same instrument on
# BOTH refresh paths, so the arm's own call count, rescan time and pair-loop
# iterations can be put beside the base's.
#
# Attribution binary only (R2).  It counts an atomic per outer iteration and
# reads the clock twice per refresh, so nothing here is a timing claim about the
# shipped build -- the timing claim is the A/B, on an uninstrumented binary.
#
# Pinned to cores 8-11, which the A/B is not using.
set -u
LIST="$1"; BUDGET="${2:-24}"; OUT="$3"
CORPUS="${LI_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
AX="${LI_M2_AX:-/data0/axeyum/lemma-input-target-measure2/release/examples/smtcomp_cli}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
: > "$OUT"
i=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  core=$((8 + i % 4))
  for arm in base arm; do
    err=$(mktemp -t "li-mech-XXXXXX")
    if [ "$arm" = arm ]; then
      AXEYUM_LIA_INITIAL_BOUND_INDEX=1 taskset -c "$core" \
        timeout $((BUDGET + 120)) "$AX" "$CORPUS/$f" \
        --timeout-ms $((BUDGET * 1000)) > /dev/null 2>"$err"
    else
      env -u AXEYUM_LIA_INITIAL_BOUND_INDEX taskset -c "$core" \
        timeout $((BUDGET + 120)) "$AX" "$CORPUS/$f" \
        --timeout-ms $((BUDGET * 1000)) > /dev/null 2>"$err"
    fi
    stats=$(grep '^; li-stats ' "$err" | tail -1 || true)
    [ -n "$stats" ] || stats="; li-stats NOREAD"
    printf '%s\t%s\t%s\n' "$f" "$arm" "${stats#; li-stats }" >> "$OUT"
    rm -f "$err"
  done
  i=$((i + 1))
done < "$LIST"
echo "rows: $(grep -c . "$LIST")   arm-runs: $(grep -c . "$OUT")"
