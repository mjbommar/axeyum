#!/usr/bin/env bash
# REAL-OPAQUE -- interleaved per-file A/B of the opaque-real-subterm abstraction.
#
# ============================ POLARITY ============================
# `AXEYUM_LRA_OPAQUE_APPS` is a KILL SWITCH. The rung SHIPS ON.
#
#   ARM "off" : AXEYUM_LRA_OPAQUE_APPS=0   = the BASE (pre-ADR-2065) ladder.
#   ARM "on"  : the variable REMOVED       = the SHIPPED arm.
#
# This is INVERTED relative to a normal opt-in flag, exactly as ADR-2025's
# `AXEYUM_ZERO_INST_SKELETON` is. A runner that gets it backwards measures the
# shipped arm in BOTH halves and reports the resulting zero as a null result.
# The "on" arm uses `env -u` rather than merely leaving the variable unset,
# because the harness environment is inherited.
# ==================================================================
#
# ONE BINARY, TWO ENV VALUES -- never two builds.
#
# Both arms run BACK TO BACK on the SAME file on the SAME pinned physical core,
# with the arm ORDER ROTATING per file, because ambient load has moved 23
# verdicts in one division at fixed code on these boxes (ADR-2000).
#
# EXIT-STATUS CHANNEL. Each run records its own outcome -- `ok`, `timeout` (the
# wrapper's SIGTERM), `rc134` (the address-space cap), `sigkill`, or `rc<n>`.
# ADR-2045's arm was `losses=0` by verdict count while creating FIVE new aborts
# on files that terminated cleanly in the base, and a verdict count cannot see
# that. A base-`ok` row that is non-`ok` in the lever arm is a LOSS even when
# both verdicts read `unknown`.
#
# MECHANISM COLUMN. Under `AXEYUM_TRACE=1` the summary line names the route that
# DECIDED and the route that BOUND the query, and a separate flag records
# whether the cause-(A) refusal text (`unsupported arithmetic atom`) appeared at
# all. An arm whose variable was silently ignored shows the same three values in
# both halves; `ab-preflight.sh` asserts they differ before any measuring starts.
#
# `lira-dpll` is NOT the route to watch, which the preflight found the hard way:
# on the first witness the abstraction unlocks `q:bool-skeleton` (ADR-2025's
# rung), whose ground checker is what was refusing. A runner hard-coded to one
# route name would have reported `absent` in both arms and called the mechanism
# column uninformative.
#
# Usage: ab-run.sh <list> <out.tsv> <core> <bin> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=${REAL_OPAQUE_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }

# Prints "<verdict>\t<ms>\t<exit>\t<route>".
#   verdict : sat | unsat | unknown | NONE
#   exit    : ok | timeout | rc134 | sigkill | rc<n>   <-- the ADR-2045 channel
#   route   : <decided_by>|<bound_by>|<refused|clean>  <-- the mechanism column
run_arm() {
  local mode="$1" f="$2" t0 t1 raw rc v ex dby bby refused
  t0=$(date +%s%N)
  if [ "$mode" = off ]; then
    raw=$(AXEYUM_LRA_OPAQUE_APPS=0 AXEYUM_TRACE=1 \
            timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$CORPUS/$f" 2>&1)
    rc=$?
  else
    raw=$(env -u AXEYUM_LRA_OPAQUE_APPS AXEYUM_TRACE=1 \
            timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$CORPUS/$f" 2>&1)
    rc=$?
  fi
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$'); v="${v:-NONE}"
  case "$rc" in
    0)   ex=ok ;;
    124) ex=timeout ;;
    134) ex=rc134 ;;
    137) ex=sigkill ;;
    *)   ex="rc$rc" ;;
  esac
  # The mechanism, read from the summary line rather than assumed:
  # which route decided, which bound, and whether the cause-(A) refusal text
  # appeared anywhere in the trace.
  dby=$(printf '%s' "$raw" | grep -oE 'decided_by=[^ ]*' | head -1 | cut -d= -f2)
  bby=$(printf '%s' "$raw" | grep -oE 'bound_by=[^ ]*' | head -1 | cut -d= -f2)
  if printf '%s' "$raw" | grep -qF 'unsupported arithmetic atom'; then
    refused=refused
  else
    refused=clean
  fi
  printf '%s\t%s\t%s\t%s|%s|%s' "$v" "$(((t1 - t0) / 1000000))" "$ex" \
    "${dby:-NONE}" "${bby:-NONE}" "$refused"
}

printf 'file\torder\toff_verdict\toff_ms\toff_exit\toff_route\ton_verdict\ton_ms\ton_exit\ton_route\n' > "$OUT"
n=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  n=$((n + 1))
  if [ $((n % 2)) -eq 1 ]; then
    ORDER="off-on"; A=$(run_arm off "$f"); B=$(run_arm on "$f")
  else
    ORDER="on-off"; B=$(run_arm on "$f"); A=$(run_arm off "$f")
  fi
  printf '%s\t%s\t%s\t%s\n' "$f" "$ORDER" "$A" "$B" >> "$OUT"
done < "$LIST"
echo "DONE $OUT rows=$n core=$PIN budget=${BUDGET}s"
