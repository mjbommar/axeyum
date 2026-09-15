#!/usr/bin/env bash
# QF-WALL -- (a) 3 passes per arm on every row the lever simulation moved, and
# (b) the instrument's NEGATIVE CONTROL.
#
# (b) is the one that can fail. The soundness of opaque-atom abstraction is an
# argument (it is a weakening); what an argument cannot establish is that THIS
# SCRIPT built the formula it claims to have built. A parser bug that dropped
# assertions would make everything `unsat` and every row would "convert".
#
# So the control is a SATISFIABLE ground query put through the same instrument:
# if the abstraction of a `sat` query comes back `unsat`, the instrument is
# manufacturing refutations and every number above it is void. The control
# query is f05's fresh-atom skeleton, which z3 and cvc5 both call `sat`.
set -u
W="$(cd "$(dirname "$0")" && pwd)"
AX=/nas3/data/axeyum/harness/qf-wall/bin/smtcomp_cli-qfwall
CVC5=/nas3/data/axeyum/harness/bin/cvc5
PIN="${1:-8}"
ax() { env AXEYUM_DECLARED_NAME_WINS=on AXEYUM_DISTINCT_LINEAR=on timeout 140 taskset -c "$PIN" "$AX" "$1" --timeout-ms 24000 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$' || true; }

echo "== (a) 3 passes per arm on the six moved rows =="
printf 'id\tbefore_1\tbefore_2\tbefore_3\tafter_1\tafter_2\tafter_3\tstability\n' > "$W/stability.tsv"
for id in f01 f03 f04 f08 f11 f12; do
  b1=$(ax "$W/skel/$id.smt2"); b2=$(ax "$W/skel/$id.smt2"); b3=$(ax "$W/skel/$id.smt2")
  a1=$(ax "$W/oatom/$id.skel.smt2"); a2=$(ax "$W/oatom/$id.skel.smt2"); a3=$(ax "$W/oatom/$id.skel.smt2")
  if [ "$b1$b2$b3" = "unknownunknownunknown" ] && [ "$a1$a2$a3" = "unsatunsatunsat" ]; then s=STABLE-GAIN
  elif [ "$b1" = "$b2" ] && [ "$b2" = "$b3" ] && [ "$a1" = "$a2" ] && [ "$a2" = "$a3" ]; then s=STABLE-OTHER
  else s=UNSTABLE; fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$id" "$b1" "$b2" "$b3" "$a1" "$a2" "$a3" "$s" >> "$W/stability.tsv"
  printf '%-4s before=%s/%s/%s  after=%s/%s/%s  %s\n' "$id" "$b1" "$b2" "$b3" "$a1" "$a2" "$a3" "$s"
done

echo
echo "== (b) negative control: a SATISFIABLE query through the same instrument =="
C="$W/skel/f05.fresh.smt2"
O="$W/oatom/control-sat.smt2"
rm -f "$O"
m=$(timeout 600 python3 "$W/opaqueatom.py" "$C" "$O" 2>&1 >/dev/null) || true
if [ ! -s "$O" ]; then echo "CONTROL DID-NOT-RUN"; exit 0; fi
zin=$(timeout 200 z3 -T:60 "$C" 2>&1 | head -1)
cin=$(timeout 200 "$CVC5" --tlimit 60000 "$C" 2>&1 | head -1)
zout=$(timeout 200 z3 -T:60 "$O" 2>&1 | head -1)
cout=$(timeout 200 "$CVC5" --tlimit 60000 "$O" 2>&1 | head -1)
axout=$(ax "$O")
printf 'control input : z3=%s cvc5=%s  (%s)\n' "$zin" "$cin" "$m"
printf 'control output: z3=%s cvc5=%s axeyum=%s\n' "$zout" "$cout" "${axout:-NONE}"
{ printf 'stage\tz3\tcvc5\taxeyum\tmeta\n'
  printf 'input\t%s\t%s\t-\t-\n' "$zin" "$cin"
  printf 'abstracted\t%s\t%s\t%s\t%s\n' "$zout" "$cout" "${axout:-NONE}" "$m"; } > "$W/control-nonvacuity.tsv"
if [ "$zin" = sat ] && [ "$zout" = unsat ]; then
  echo "CONTROL FAILED -- the instrument manufactured a refutation"; exit 1
fi
if [ "$zin" = sat ] && [ "$zout" = sat ]; then
  echo "CONTROL PASSED -- a satisfiable query stays satisfiable through the instrument"
else
  echo "CONTROL INCONCLUSIVE -- input z3=$zin output z3=$zout"
fi
