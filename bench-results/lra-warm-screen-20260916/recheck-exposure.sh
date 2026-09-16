#!/usr/bin/env bash
# ADR-2132: when the exposure queues finish, re-check every raw mover they
# produced, 3x per arm, then stop.
#
# Derived from the finished exposure TSVs rather than typed, same as the QF_LRA
# rechecks. `off` vs `screened` only: those runs have no `on` arm.
set -u
cd ~/lra-warm-screen || exit 2

waited=0
while [ "$(cat exposure00.log exposure01.log 2>/dev/null | grep -c EXPOSURE-DONE)" -lt 2 ]; do
  if [ "$waited" -ge 10800 ]; then
    echo "ABORT: exposure queues did not finish within 3h; no recheck started"
    exit 2
  fi
  sleep 60
  waited=$((waited + 60))
done
echo "exposure queues done after ${waited}s $(date -Is)"

awk -F'\t' '
  FNR==1 { for (i=1;i<=NF;i++) h[$i]=i; next }
  {
    a=$(h["a_verdict"]); c=$(h["c_verdict"]);
    ad = (a=="sat" || a=="unsat"); cd = (c=="sat" || c=="unsat");
    if (ad != cd) print $1;
    else if (ad && cd && a != c) print $1;
  }' ab3.QF_LIA.*.tsv ab3.QF_UFLRA.*.tsv ab3.QF_UFLIA.*.tsv ab3.QF_IDL.*.tsv ab3.QF_RDL.*.tsv \
  | sort -u > movers.exposure.txt

n=$(wc -l < movers.exposure.txt)
echo "exposure movers: $n"
cat movers.exposure.txt
if [ "$n" -eq 0 ]; then echo "EXPOSURE-RECHECK-DONE 0 movers"; exit 0; fi

./recheck-movers-2132.sh movers.exposure.txt recheck.exposure.tsv 5,13 ./axeyum.v1 off screened 24
echo "EXPOSURE-RECHECK-DONE"
