#!/usr/bin/env bash
# QUANT-SESSION-ARITH (ADR-2130) -- how often does the lever actually ENGAGE?
#
#   engagement-probe.sh <bin> <list> <level> [budget_s]
#
# Runs one arm over a core list and prints, per core, the session-construction
# site's own line. This is the cheap question that has to be answered BEFORE the
# paired probe: a lever that hosts arithmetic on 0 cores produces a null that
# looks exactly like a lever that hosts it on 53 and does not help.
#
# Three outcomes are distinguished and none is folded into another:
#   NO-LINE    the site was never reached -- the loop exited first.  An ABSENCE.
#   DECLINED   the site ran and `OnlineQuantifierClauseSession::new` returned None.
#   built=1    a session exists; `hosted=` says whether it hosts arithmetic.
set -u
AX="$1"; LIST="$2"; LEVEL="$3"; BUDGET="${4:-24}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

reached=0; built=0; host=0; total=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  total=$((total + 1))
  err="$(mktemp)"
  if [ "$LEVEL" = "unset" ]; then
    env -u AXEYUM_QINST_GROUND_SESSION AXEYUM_QTRACE=1 \
      timeout $((BUDGET + 16)) "$AX" "$f" --trace --timeout-ms $((BUDGET * 1000)) \
      > /dev/null 2> "$err"
  else
    AXEYUM_QINST_GROUND_SESSION="$LEVEL" AXEYUM_QTRACE=1 \
      timeout $((BUDGET + 16)) "$AX" "$f" --trace --timeout-ms $((BUDGET * 1000)) \
      > /dev/null 2> "$err"
  fi
  line="$(grep -m1 'ground-session' "$err" || true)"
  rm -f "$err"
  name="$(basename "$f")"
  if [ -z "$line" ]; then
    echo "NO-LINE   ${name:0:70}"
  else
    reached=$((reached + 1))
    case "$line" in
      *"built=1"*) built=$((built + 1)) ;;
    esac
    case "$line" in
      *"hosted=1"*) host=$((host + 1)) ;;
    esac
    echo "$(echo "$line" | sed 's/^\[qtrace\] ground-session //')   ${name:0:50}"
  fi
done < "$LIST"

echo
echo "level=$LEVEL  cores=$total  site reached=$reached  session built=$built  HOSTING=$host"
