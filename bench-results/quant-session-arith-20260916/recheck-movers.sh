#!/usr/bin/env bash
# QUANT-SESSION-ARITH (ADR-2130) -- re-run each mover N times per arm to
# separate a STABLE move from ambient load.
#
#   recheck-movers.sh <bin> <movers.list> <outdir> <on_level> [passes] [budget_s]
#
# One pinned core, nothing else on it, and the arms ALTERNATE WITHIN a pass
# rather than running all of one arm and then all of the other -- the same rule
# the paired probe follows, for the same reason: arm-after-arm puts the two arms
# in different load regimes.
#
# A raw mover is not a result. ADR-2124's own re-check turned 2 raw gains into 1
# stable and 1 ambient, and 6 raw losses into 5 stable and 1 ambient.
set -u
AX="$1"; LIST="$2"; OUT="$3"; ON_LEVEL="$4"; PASSES="${5:-3}"; BUDGET="${6:-24}"
PIN="${PIN:-1,9}"
mkdir -p "$OUT"
TSV="$OUT/movers-recheck.tsv"
printf 'core\tpass\toff_verdict\ton_verdict\n' > "$TSV"

verdict_of() {  # $1 = out file
  sed -n 's/.*"verdict"[[:space:]]*:[[:space:]]*"\([a-z]*\)".*/\1/p' "$1" | tail -1
}

while IFS= read -r f; do
  [ -n "$f" ] || continue
  name="$(basename "$f")"
  for pass in $(seq 1 "$PASSES"); do
    for arm in off on; do
      o="$OUT/$name.$arm.$pass.out"
      if [ "$arm" = "off" ]; then
        env -u AXEYUM_QINST_GROUND_SESSION \
          timeout $((BUDGET + 16)) taskset -c "$PIN" \
          "$AX" "$f" --trace --timeout-ms $((BUDGET * 1000)) > "$o" 2>/dev/null
      else
        AXEYUM_QINST_GROUND_SESSION="$ON_LEVEL" \
          timeout $((BUDGET + 16)) taskset -c "$PIN" \
          "$AX" "$f" --trace --timeout-ms $((BUDGET * 1000)) > "$o" 2>/dev/null
      fi
    done
    ov="$(verdict_of "$OUT/$name.off.$pass.out")"
    nv="$(verdict_of "$OUT/$name.on.$pass.out")"
    printf '%s\t%s\t%s\t%s\n' "$name" "$pass" "${ov:-none}" "${nv:-none}" >> "$TSV"
  done
done < "$LIST"

echo "wrote $TSV"
cat "$TSV"
