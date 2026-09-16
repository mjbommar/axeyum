#!/usr/bin/env bash
# Re-run the A/B's one mover three times per arm, interleaved, on one pinned
# pair of an idle box. A single-run verdict difference is not a mover until it
# reproduces; a 24 s budget and a ~12 s solve are one scheduling hiccup apart.
set -u
BIN=/nas3/data/axeyum/lanes/quant-instance-select/smtcomp_cli_ladder
F=/nas3/data/axeyum/harness/core-select/cores/UFLIA_boogie_Cast_Cast.R_System.Object_System.Int32.smt2.core.smt2
for i in 1 2 3; do
  for arm in off on; do
    if [ "$arm" = off ]; then L=0; else L=1; fi
    v=$( ( ulimit -v 8388608
           AXEYUM_QINST_GEN_LADDER=$L timeout -k 5 40 taskset -c 1,9 \
             "$BIN" "$F" --timeout-ms 24000 ) 2>/dev/null \
         | grep -E '^(sat|unsat|unknown)$' | tail -1 )
    printf 'run=%d arm=%s verdict=%s\n' "$i" "$arm" "${v:-NONE}"
  done
done
