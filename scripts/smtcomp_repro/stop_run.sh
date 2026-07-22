#!/usr/bin/env bash
# Cleanly stop a distributed inventory run WITHOUT orphaning solver children.
#
# The failure that cooked the fleet earlier: `pkill -f compete.py` killed the
# parent runners but left their axeyum-smtcomp children running — and axeyum's
# internal --timeout-ms does not fire on some hard files, so the orphans ran
# unbounded and piled up. The fix: kill the children FIRST (so parents move on
# and stop spawning), then the parents, then sweep any stragglers.
#
# Usage: stop_run.sh [host ...]   (default: s4 s5 s6 s7)
set -uo pipefail
HOSTS=("${@:-s4 s5 s6 s7}")
for h in ${HOSTS[@]}; do
  ssh -o BatchMode=yes "$h" '
    pkill -9 -f "compete.py --file-list" 2>/dev/null   # stop spawners first
    pkill -9 -x axeyum-smtcomp 2>/dev/null              # then all solver children
    sleep 2
    pkill -9 -x axeyum-smtcomp 2>/dev/null              # sweep any mid-spawn
    echo -n "'"$h"' clean: axeyum="; pgrep -xc axeyum-smtcomp
  ' 2>&1 | sed "s/^/[$h] /"
done
