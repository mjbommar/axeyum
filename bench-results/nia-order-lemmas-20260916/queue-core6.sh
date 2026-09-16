#!/usr/bin/env bash
# Core 6's serial queue: wait for the QF_NRA control sweep, then UFNIA.
# Lane NIA-ORDER-LEMMAS, ADR-2136.
#
# `QF_NRA` is a CONTROL and not a target: the lever sits in the INTEGER
# nonlinear route, so a Real-sorted query should not reach it and any movement
# there is a finding about reach rather than about the lever. `UFNIA` is a
# target -- ADR-2106 measured losses in `q:skolem-qf`'s hand-off to the
# quantifier-free ladder, so the nonlinear integer tail really is reached from
# a quantified query.
#
# The wait is on the sweep's own DONE line in its log, not on a process match.
set -uo pipefail
cd "$(dirname -- "${BASH_SOURCE[0]}")" || exit 2
BUDGET=${1:-24}

while ! grep -q "^AB-DONE QF_NRA " out/ab-QF_NRA.log 2>/dev/null; do sleep 30; done
echo "core6: QF_NRA done, starting UFNIA"

./ab-run-env.sh UFNIA lists/ab-list-UFNIA.txt out/ab-UFNIA.tsv 6 ./smtcomp_cli \
    "AXEYUM_NIA_ORDER_LEMMAS=0" "AXEYUM_NIA_ORDER_LEMMAS=1" "$BUDGET"
echo "CORE6-QUEUE-DONE"
