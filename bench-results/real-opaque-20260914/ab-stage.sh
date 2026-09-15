#!/usr/bin/env bash
# REAL-OPAQUE -- copy the runner and the lists to the SHARED path the compute
# hosts can see, and print the digest of what was staged.
#
# The lane worktree lives under the dev box's home directory and is NOT visible
# from s5/s6/s7. The first launch attempt discovered this the expensive way: four
# `No such file or directory` lines in four logs, zero TSV rows, and a launcher
# that printed "launched" four times. Staging is a separate step so that the
# digest of the runner actually in use can be read back and compared.
#
# Usage: ab-stage.sh <lane-root>
set -eu
ROOT="$1"
W="$ROOT/bench-results/real-opaque-20260914"
RUN=/nas3/data/axeyum/harness/real-opaque/run
mkdir -p "$RUN/lists"
cp "$W/ab-run.sh" "$RUN/ab-run.sh"
cp "$W"/lists/*.list "$RUN/lists/"
echo "staged runner:"
sha256sum "$W/ab-run.sh" "$RUN/ab-run.sh"
echo "staged lists:"
wc -l "$RUN"/lists/*.list
