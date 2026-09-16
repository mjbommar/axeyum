#!/usr/bin/env bash
# Interleaved shipped-vs-gate<N> ladder rung, through scripts/ledger-run-one.sh,
# one shard. Lane NIA-GROEBNER-GATE (ADR-2112 Part F probe).
#
# Two ledger rows per file (arm=shipped, arm=gate<N>), alternating which arm
# runs first per file so ambient load cancels in the difference rather than
# landing on whichever arm runs second.
#
# usage: run-arm-pair.sh <rung_n_or_label> <lever_value_or_empty> <list> <core> <sweep_id_suffix>
#   lever_value empty means "shipped only" (used for the QF_NRA/UFNIA shipped baseline run,
#   where we still want an arm=shipped row but no arm=gateN row).
set -u
HERE=/home/mjbommar/nia-groebner-gate-20260915
BIN=$HERE/bin/smtcomp_cli
BIN_SHA=3c3ba0eb2
CORPUS_ROOT=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/
LEDGER_DIR=$HERE/ledger
CAPTURES=$HERE/captures

LABEL=${1:?rung label}
LEVER=${2-}
LIST=${3:?list}
CORE=${4:?core}
SWEEP_SUFFIX=${5:?sweep suffix}
BUDGET=24
HEADROOM=16
VLIM=$((8 * 1024 * 1024))

SWEEP_ID="nia-groebner-gate-${SWEEP_SUFFIX}"
OUT_LOG=$HERE/run-${LABEL}-core${CORE//,/_}.log

[ -x "$BIN" ] || { echo "ABORT: $BIN missing"; exit 2; }
[ -s "$LIST" ] || { echo "ABORT: $LIST missing/empty"; exit 2; }

n=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  n=$((n + 1))
  if [ -z "$LEVER" ]; then
    # shipped-only pass (used for control divisions' baseline row)
    env -u AXEYUM_MAX_IDEAL_GENERATORS -u AXEYUM_MAX_IDEAL_ATOMS -u AXEYUM_MAX_IDEAL_INEQUALITIES \
      "$HERE/scripts/ledger-run-one.sh" --sweep-id "$SWEEP_ID" --arm shipped \
      --binary "$BIN" --binary-sha "$BIN_SHA" --file "$f" --corpus-root "$CORPUS_ROOT" \
      --outdir "$CAPTURES/$SWEEP_SUFFIX" --ledger-dir "$LEDGER_DIR" \
      --budget-s $BUDGET --headroom-s $HEADROOM --vlimit-kb $VLIM \
      --core "$CORE" --host server7 --note "nia-groebner-gate shipped-only $LABEL" \
      >> "$OUT_LOG" 2>&1
  else
    run_shipped() {
      env -u AXEYUM_MAX_IDEAL_GENERATORS -u AXEYUM_MAX_IDEAL_ATOMS -u AXEYUM_MAX_IDEAL_INEQUALITIES \
        "$HERE/scripts/ledger-run-one.sh" --sweep-id "$SWEEP_ID" --arm shipped \
        --binary "$BIN" --binary-sha "$BIN_SHA" --file "$f" --corpus-root "$CORPUS_ROOT" \
        --outdir "$CAPTURES/$SWEEP_SUFFIX" --ledger-dir "$LEDGER_DIR" \
        --budget-s $BUDGET --headroom-s $HEADROOM --vlimit-kb $VLIM \
        --core "$CORE" --host server7 --note "nia-groebner-gate ladder $LABEL" \
        >> "$OUT_LOG" 2>&1
    }
    run_gate() {
      env AXEYUM_MAX_IDEAL_GENERATORS="$LEVER" AXEYUM_MAX_IDEAL_ATOMS="$LEVER" AXEYUM_MAX_IDEAL_INEQUALITIES="$LEVER" \
        "$HERE/scripts/ledger-run-one.sh" --sweep-id "$SWEEP_ID" --arm "gate${LABEL}" \
        --binary "$BIN" --binary-sha "$BIN_SHA" --file "$f" --corpus-root "$CORPUS_ROOT" \
        --outdir "$CAPTURES/$SWEEP_SUFFIX" --ledger-dir "$LEDGER_DIR" \
        --budget-s $BUDGET --headroom-s $HEADROOM --vlimit-kb $VLIM \
        --core "$CORE" --host server7 --note "nia-groebner-gate ladder $LABEL" \
        >> "$OUT_LOG" 2>&1
    }
    if [ $((n % 2)) -eq 1 ]; then run_shipped; run_gate; else run_gate; run_shipped; fi
  fi
  echo "PROGRESS $LABEL core=$CORE $n files" >> "$OUT_LOG"
done < "$LIST"
echo "ARM-PAIR-DONE $LABEL core=$CORE $n files -> sweep=$SWEEP_ID" >> "$OUT_LOG"
echo "ARM-PAIR-DONE $LABEL core=$CORE $n files -> sweep=$SWEEP_ID"
