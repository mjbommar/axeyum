#!/usr/bin/env bash
# DT-QUANT-TRACE -- attribute each core to ONE z3 engine, and read z3's own
# datatype-axiom counters.
#
#   ref-trace.sh <list-of-.smt2> <outdir> <pin> [tlimit_s]
#
# FOUR runs per file, not three. A `-st` line from the DEFAULT configuration
# cannot say WHICH engine closed the goal -- e-matching and MBQI both run --
# so the attribution is the ABLATIONS. But two ablations are not enough
# either: a core that both single-ablation runs decide is NOT "decided by
# either engine" until the BOTH-OFF control says the quantifier engines were
# needed at all. Without that control every ground-refutable core reports
# EITHER and the census manufactures an attribution for rows where no
# quantifier reasoning happened. That is the whole reason this arm exists.
#
#   default        smt.ematching on     smt.mbqi on
#   emat_only      smt.ematching on     smt.mbqi=false
#   mbqi_only      smt.ematching=false  smt.mbqi on
#   neither        smt.ematching=false  smt.mbqi=false      <- the CONTROL
#
# Attribution, in this order:
#   GROUND     the both-off control already decides it; no quantifier engine
#              is responsible and the two ablation columns say nothing.
#   EITHER     both single ablations decide it, the control does not.
#   EMATCHING  only the e-matching ablation decides it.
#   MBQI       only the MBQI ablation decides it.
#   SYNERGY    the default decides it and neither ablation does.
#   UNDECIDED  the default does not decide it.
#
# Timing is z3's OWN `:total-time`, not a shell clock: `date +%3N` is silently
# unsupported on this host and returns nanoseconds, which this script printed
# as a 19-digit millisecond count on its first run.
#
# `datatype-constructor-ax` / `datatype-accessor-ax` are z3's own counters for
# the axioms `theory_datatype` instantiated. They are the direct answer to
# "what does z3 do with the construct we refuse", read from z3 rather than
# inferred from its source.
#
# Argument order matches `ax-trace.sh` so `launch.sh` can shard either runner
# without a per-runner special case -- the `<bin>` slot is the SOLVER for both,
# and a launcher that reordered arguments per runner is a place for the two to
# drift apart silently.
set -u
LIST="$1"; OUT="$2"; PIN="$3"; Z3="${4:-z3}"; TL="${5:-60}"
# Slot 4 is the solver, so `launch.sh` must be given `DT_AX=/usr/bin/z3` for
# this runner. Refuse anything that is not z3 rather than trying to be helpful:
# a run that silently fell back to `z3` while the caller believed it had pinned
# a build is a measurement of the wrong binary.
case "$("$Z3" --version 2>&1 | head -1)" in
  Z3\ version*) ;;
  *) echo "ABORT: '$Z3' is not z3 (pass DT_AX=/usr/bin/z3)"; exit 2 ;;
esac
echo "reference: $("$Z3" --version 2>&1 | head -1) at $Z3"
OUTDIR="$(dirname "$OUT")"
mkdir -p "$OUTDIR/logs"

printf 'file\tdefault\temat_only\tmbqi_only\tneither\tattribution\tqi_inst\tmax_gen\tnum_checks\tdt_ctor_ax\tdt_acc_ax\tconflicts\tz3_total_s\n' > "$OUT"

stat_of() { printf '%s\n' "$2" | sed -n "s/^ *:\{0,1\}$1  *\([0-9.]*\).*/\1/p" | head -1; }

verdict() {  # <file> <extra z3 args...>
  local f="$1"; shift
  taskset -c "$PIN" timeout $((TL + 20)) "$Z3" -T:"$TL" "$@" "$f" 2>&1 \
    | grep -m1 -oE '^(sat|unsat|unknown|timeout)$' || echo NOVERDICT
}

while IFS= read -r f; do
  [ -n "$f" ] || continue
  b=$(basename "$f")
  raw=$(taskset -c "$PIN" timeout $((TL + 20)) "$Z3" -T:"$TL" -st "$f" 2>&1)
  printf '%s\n' "$raw" > "$OUTDIR/logs/$b.default.log"
  d=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown|timeout)$' || echo NOVERDICT)

  qi=$(stat_of quant-instantiations "$raw")
  mg=$(stat_of max-generation "$raw")
  nc=$(stat_of num-checks "$raw")
  dc=$(stat_of datatype-constructor-ax "$raw")
  da=$(stat_of datatype-accessor-ax "$raw")
  cf=$(stat_of conflicts "$raw")
  tt=$(stat_of total-time "$raw")

  e=$(verdict "$f" smt.mbqi=false)
  m=$(verdict "$f" smt.ematching=false)
  n=$(verdict "$f" smt.ematching=false smt.mbqi=false)

  decided() { [ "$1" = unsat ] || [ "$1" = sat ]; }
  if ! decided "$d"; then a=UNDECIDED
  elif decided "$n"; then a=GROUND
  elif decided "$e" && decided "$m"; then a=EITHER
  elif decided "$e"; then a=EMATCHING
  elif decided "$m"; then a=MBQI
  else a=SYNERGY
  fi

  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$b" "$d" "$e" "$m" "$n" "$a" \
    "${qi:-0}" "${mg:-0}" "${nc:-0}" "${dc:-0}" "${da:-0}" "${cf:-0}" "${tt:-NA}" >> "$OUT"
done < "$LIST"
echo "DONE $OUT"
