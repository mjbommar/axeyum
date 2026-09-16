#!/usr/bin/env bash
# ADR-2132: when both `QF_LRA` shards finish -- re-check every mover 3x per arm,
# THEN start the exposure queues. In that order, and without a human in between.
#
# # Why the recheck must come first
#
# A raw mover is not a finding. The ship criteria turn on STABLE losses, and
# "stable" means the 3x-per-arm recheck agrees; [ADR-1966] had 11 of its 18
# movers vanish under exactly this procedure. So the recheck is criteria 2 and 3
# and the exposure queue is criterion 4 -- and the recheck takes about twenty
# minutes against the exposure queue's several hours.
#
# Running the exposure queue first would leave the recheck waiting behind it on
# the same two core pairs, which is how a short essential measurement ends up
# reported as "did not run" behind a long optional one.
#
# # The mover list is DERIVED here, not typed
#
# Deriving it from the finished TSVs rather than pasting the four paths a
# partial run happened to show is the whole point: the last rows of each shard
# can add movers, and a list typed from a partial is a list of the movers
# somebody looked at. It is computed for BOTH comparisons -- `off` vs `screened`
# (the ship decision) and `off` vs `on` (ADR-2125's arm, the reference) -- and
# their union is what gets re-checked, because a row that moves in either is a
# row whose stability the tables depend on.
#
# Usage: chain-recheck-then-exposure.sh <bin> [max_wait_s]
set -u
AX="$1"; MAXWAIT="${2:-21600}"

waited=0
while ! { grep -q 'AB3-DONE' LRApin.log 2>/dev/null && grep -q 'AB3-DONE' LRAheld.log 2>/dev/null; }; do
  if [ "$waited" -ge "$MAXWAIT" ]; then
    echo "ABORT: both shards did not print AB3-DONE within ${MAXWAIT}s -- nothing further started"
    exit 2
  fi
  sleep 60
  waited=$((waited + 60))
done
echo "CHAIN: both QF_LRA shards done after ${waited}s $(date -Is)"

# The movers, derived. A row MOVED if exactly one of the two arms decided it, or
# if both decided it differently.
derive() {  # $1 = treatment column prefix (b|c)
  awk -F'\t' -v arm="$1" '
    NR==1 { for (i=1;i<=NF;i++) h[$i]=i; next }
    {
      a=$(h["a_verdict"]); t=$(h[arm "_verdict"]);
      ad = (a=="sat" || a=="unsat"); td = (t=="sat" || t=="unsat");
      if (ad != td) print $1;
      else if (ad && td && a != t) print $1;
    }' ab3.LRApin.tsv ab3.LRAheld.tsv
}
{ derive b; derive c; } | sort -u > movers.2132.txt
n=$(wc -l < movers.2132.txt)
echo "CHAIN: $n distinct movers across both comparisons and both draws"
cat movers.2132.txt

if [ "$n" -gt 0 ]; then
  # Two arm pairs, one per core pair, in parallel. Each is its own comparison
  # and neither shares a row's run with the other.
  ( ./recheck-movers-2132.sh movers.2132.txt recheck.off-screened.tsv 5,13 "$AX" off screened 24 \
      > recheck-off-screened.log 2>&1 ) &
  ( ./recheck-movers-2132.sh movers.2132.txt recheck.off-on.tsv 6,14 "$AX" off on 24 \
      > recheck-off-on.log 2>&1 ) &
  wait
  echo "CHAIN: rechecks done $(date -Is)"
  tail -2 recheck-off-screened.log recheck-off-on.log
else
  echo "CHAIN: no movers to re-check"
fi

echo "CHAIN: starting the exposure queues $(date -Is)"
( ./launch-exposure.sh 00 5,13 "$AX" > exposure00.log 2>&1 ) &
( ./launch-exposure.sh 01 6,14 "$AX" > exposure01.log 2>&1 ) &
wait
echo "CHAIN: exposure queues done $(date -Is)"
