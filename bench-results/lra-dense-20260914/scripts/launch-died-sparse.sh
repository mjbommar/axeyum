#!/usr/bin/env bash
# The 15 rows that die INSIDE the round-trip row-build loop, re-run under the
# SPARSE arm so they can report the shape they were building.
#
# These 15 reach `simplex-fallback-entry` and never reach `dense-rows-built`:
# the process dies while materialising the dense `m x nvars` matrix, so `m` and
# `tableau_cells` are never printed and the post-removal requirement is UNKNOWN
# for them.  They are also exactly the rows where the round trip is most likely
# to be decisive, so leaving them out of the prediction would leave the lever's
# best case unmeasured.
#
# Under AXEYUM_LRA_SPARSE_ROWS=1 the row build is O(nnz) and cannot be what
# kills them, so they get far enough to print the tableau they would need.
set -u
L=/nas3/data/axeyum/harness/lra-dense
BIN=$L/bin/smtcomp_cli-4abc994a0

launch() {  # $1=host $2=shard $3=pin
  ssh -o BatchMode=yes "$1" \
    "AXEYUM_LRA_SPARSE_ROWS=1 nohup setsid bash $L/scripts/profile-run.sh dsh$2 \
       $L/lists/DIED.sh$2.txt $L/out/died.sh$2.tsv $L/logs/died-sh$2 $3 $BIN 24 \
       > $L/logs/died.sh$2.log 2>&1 < /dev/null &" \
    && echo "launched died-sparse shard $2 on $1 pin $3"
}

launch s5 0 0,8
launch s5 1 1,9
launch s6 2 0,8
launch s6 3 1,9
launch s7 4 0,8
launch s7 5 1,9
echo "ALL_LAUNCHED"
