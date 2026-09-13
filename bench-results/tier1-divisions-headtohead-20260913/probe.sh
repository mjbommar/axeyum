#!/usr/bin/env bash
# LIVE PROBE, run on every board host BEFORE any measurement.
#
# Each of the three solvers must DECIDE at least one file, on this host, with
# the exact binaries and flags the board will use.  BOARD-FPBV records that z3
# was absent on a host once and 800 files scored a silent 0/200 that read
# exactly like a result: a missing binary and a hard division produce the same
# TSV.  This is the check that tells them apart, and it fails loudly.
#
# It probes the FIRST file of each division's pinned list -- not a file chosen
# for being easy -- and requires that ACROSS the seven divisions each solver
# decided something.  A per-division decision is not required: a solver may
# legitimately decide nothing in one division, which is the result, not a fault.
set -u
H=/nas3/data/axeyum/harness/tier1-divisions
AX=$H/bin/smtcomp_cli
Z3=/usr/bin/z3
CVC5=/nas3/data/axeyum/harness/bin/cvc5
B=10

for b in "$AX" "$Z3" "$CVC5"; do
  [ -x "$b" ] || { echo "PROBE-ABORT on $(hostname): $b missing"; exit 2; }
done

declare -A HIT=([axeyum]=0 [z3]=0 [cvc5]=0)
for d in AUFLIRA UFNIA ABV ALIA AUFNIRA AUFBV FP; do
  f=$(head -1 "$H/lists/$d.s0")
  a=$(timeout 30 "$AX" "$f" --timeout-ms $((B * 1000)) 2>/dev/null | grep -m1 -oE '^(sat|unsat)$')
  z=$(timeout 30 "$Z3" -T:$B "$f" 2>/dev/null | grep -m1 -oE '^(sat|unsat)$')
  c=$(timeout 30 "$CVC5" --tlimit=$((B * 1000)) "$f" 2>/dev/null | grep -m1 -oE '^(sat|unsat)$')
  [ -n "$a" ] && HIT[axeyum]=1
  [ -n "$z" ] && HIT[z3]=1
  [ -n "$c" ] && HIT[cvc5]=1
  printf '%-10s axeyum=%-7s z3=%-7s cvc5=%-7s\n' "$d" "${a:-unknown}" "${z:-unknown}" "${c:-unknown}"
done

bad=0
for s in axeyum z3 cvc5; do
  [ "${HIT[$s]}" = 1 ] || { echo "PROBE-FAIL on $(hostname): $s decided NOTHING in seven divisions"; bad=1; }
done
[ "$bad" = 0 ] && echo "PROBE-OK on $(hostname): all three solvers are live"
exit "$bad"
