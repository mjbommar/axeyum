#!/usr/bin/env bash
# REAL-OPAQUE preflight -- the two arms MUST differ by MECHANISM before any
# measuring starts.
#
# A lever that is read through a `OnceLock`, spelled wrong, compiled out, or
# whose polarity the runner has backwards produces an A/B where both arms are
# the same binary behaviour and the zero is reported as a null. This runs one
# known cause-(A) witness through both arms and requires the `lira-dpll` trail
# line to DIFFER.
#
# Usage: ab-preflight.sh <bin> [file]
set -u
AX="$1"
CORPUS=${REAL_OPAQUE_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}
F="${2:-AUFLIRA/nasa/fol_simplify_array_only/gauss_array_0490.fof.smt2}"

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -r "$CORPUS/$F" ] || { echo "ABORT: $CORPUS/$F unreadable"; exit 2; }

probe() {
  local raw
  raw=$("$@" AXEYUM_TRACE=1 timeout 60 "$AX" "$CORPUS/$F" --timeout-ms 24000 2>&1)
  local v dby refused
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$'); v="${v:-NONE}"
  dby=$(printf '%s' "$raw" | grep -oE 'decided_by=[^ ]*' | head -1 | cut -d= -f2)
  if printf '%s' "$raw" | grep -qF 'unsupported arithmetic atom'; then refused=refused
  else refused=clean; fi
  printf '%s/%s/%s' "$v" "${dby:-NONE}" "$refused"
}

OFF=$(probe env AXEYUM_LRA_OPAQUE_APPS=0)
ON=$(probe env -u AXEYUM_LRA_OPAQUE_APPS)
echo "file : $F"
echo "off  : $OFF   (AXEYUM_LRA_OPAQUE_APPS=0, the BASE arm)"
echo "on   : $ON    (variable REMOVED, the SHIPPED arm)"
if [ "$OFF" = "$ON" ]; then
  echo "PREFLIGHT-FAIL: the arms are indistinguishable on this witness."
  echo "  Either the lever is not read, the polarity is inverted in the runner,"
  echo "  or this file is not a cause-(A) row. Do NOT measure."
  exit 1
fi
echo "PREFLIGHT-OK: the arms differ by mechanism."
