#!/usr/bin/env bash
# QUANT-ACTIVATION -- does the lever REACH its own target on the real corpus?
#
#   reach-probe.sh <list> <out.tsv> <pin> <bin> [budget_s]
#
# The A/B measures whether the lever CONVERTS a file. This measures the step
# before: whether a widened registration is produced and HANDED OFF at all. The
# two can disagree in the way that matters -- a lever that reaches its target and
# does not convert is a capability question, while one that never reaches it is
# a plumbing failure reported as a null, and a sweep that prints `+0` cannot tell
# them apart.
#
# The observable is `AXEYUM_QPROBE`'s per-universal line:
#
#   rej_nocontext  the universal is a registration with NO context -- its tuples
#                  are joined and then DISCARDED. What ADR-2113 measured at
#                  100.0 % of 2,139,815 rejections.
#   rej_handoff    the universal HAS a context, so its tuples were handed to the
#                  positive-replacement driver instead of dropped.
#
# So the lever reaching its target is exactly `rej_handoff` rising from arm A to
# arm B, and the file's `rej_nocontext` falling. Both columns are printed for
# both arms, because a rise in one without a fall in the other would mean the
# rows being counted are not the rows the widening moved.
#
# `AXEYUM_QPROBE_CENSUS=1` is required ON TOP of `AXEYUM_QPROBE=1`: without it
# every `rej_*` field prints 0 (`AdmissionCensus::enabled` is the AND of the
# two), and reading those zeros as "nothing was rejected" attributes a cause to
# a measurement nobody took (ADR-2113 §6).
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }

arm() {  # $1 = "" for the shipped arm, else the level
  local err nocontext handoff verdict
  err=$(mktemp)
  if [ -z "$1" ]; then
    verdict=$(env -u AXEYUM_QINST_POSITIVE_PATH AXEYUM_QPROBE=1 AXEYUM_QPROBE_CENSUS=1 \
        timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
        bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
        "$AX" "$f" 2>"$err" | grep -m1 -oE '^(sat|unsat|unknown)$')
  else
    verdict=$(AXEYUM_QINST_POSITIVE_PATH="$1" AXEYUM_QPROBE=1 AXEYUM_QPROBE_CENSUS=1 \
        timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
        bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
        "$AX" "$f" 2>"$err" | grep -m1 -oE '^(sat|unsat|unknown)$')
  fi
  nocontext=$(grep -oE 'rej_nocontext=[0-9]+' "$err" | cut -d= -f2 \
                | awk '{s += $1} END {print s + 0}')
  handoff=$(grep -oE 'rej_handoff=[0-9]+' "$err" | cut -d= -f2 \
              | awk '{s += $1} END {print s + 0}')
  # Whether the probe printed AT ALL is its own column: a file whose loop exits
  # before the probe block is NOT a file with zero handoffs, and collapsing the
  # two is how a census reports a strong negative it never measured.
  probed=$(grep -cE '^QPROBE   universal\[' "$err")
  rm -f "$err"
  printf '%s\t%s\t%s\t%s' "${verdict:-none}" "$probed" "$nocontext" "$handoff"
}

printf 'file\tA_verdict\tA_probed\tA_nocontext\tA_handoff\tB_verdict\tB_probed\tB_nocontext\tB_handoff\n' > "$OUT"
while read -r f; do
  [ -z "$f" ] && continue
  case "$f" in /*) : ;; *) f="$CORPUS$f" ;; esac
  a=$(arm ""); b=$(arm 1)
  printf '%s\t%s\t%s\n' "${f#"$CORPUS"}" "$a" "$b" >> "$OUT"
done < "$LIST"
echo "REACH-DONE -> $OUT"
