#!/usr/bin/env bash
# Core 5's serial queue: wait for the reachability probe, then QF_NIA (pinned),
# then the HELD-OUT QF_NIA draw. Lane NIA-ORDER-LEMMAS, ADR-2136.
#
# Divisions run SERIALLY on one physical core rather than in parallel across
# hyperthread siblings: two shards on 5 and 13 share one physical core, which
# halves each shard's throughput and puts the two arms of DIFFERENT files on
# one core -- exactly the contention the per-file interleaving exists to
# cancel.
#
# The wait is on the probe's OUTPUT ARTIFACT, not on a `pgrep` of its command
# line: a `while pgrep -f 'reachability'` inside a shell whose own cmdline
# contains that string never exits.
set -uo pipefail
cd "$(dirname -- "${BASH_SOURCE[0]}")" || exit 2
BUDGET=${1:-24}

while ! grep -q "^REACHABILITY " out/reach.log 2>/dev/null; do sleep 30; done
echo "core5: reachability done, starting QF_NIA"

./ab-run-env.sh QF_NIA lists/ab-list-QF_NIA.txt out/ab-QF_NIA.tsv 5 ./smtcomp_cli \
    "AXEYUM_NIA_ORDER_LEMMAS=0" "AXEYUM_NIA_ORDER_LEMMAS=1" "$BUDGET"
echo "core5: QF_NIA done, starting the HELD-OUT QF_NIA draw"

./ab-run-env.sh QF_NIA-heldout lists/heldout-QF_NIA.txt out/ab-QF_NIA-heldout.tsv 5 \
    ./smtcomp_cli "AXEYUM_NIA_ORDER_LEMMAS=0" "AXEYUM_NIA_ORDER_LEMMAS=1" "$BUDGET"
echo "CORE5-QUEUE-DONE"
