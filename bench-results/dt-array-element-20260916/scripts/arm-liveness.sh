#!/usr/bin/env bash
# DT-ARRAY-ELEMENT -- THE ARM-LIVENESS CONTROL, and it is not optional.
#
#   arm-liveness.sh [bin]
#
# `ab-summarize.py` prints, on an all-agreeing A/B:
#
#   "the two arms agree on every row. That is consistent with the lever
#    changing nothing on this population AND with the arm never having been
#    enabled -- the two are not distinguishable from this file."
#
# This is the file that distinguishes them, and it does it on the ONE
# observable that cannot be produced by an inert arm: the W1 refusal sentence
# `register_datatype` emits. If the lever is live, the ON arm emits ZERO of
# them on a file the OFF arm emits many; if the lever were inert the two counts
# would be equal. The two files are the only two undecided `AUFDTLIRA` rows
# whose TERMINAL reason is that refusal
# (`bench-results/dt-array-element-20260916/README.md` §2).
#
# Exit status depends on the finding: 0 only when every file shows base>0 and
# arm==0. A control that always exits 0 is the checker that cannot fail.
set -u
AX="${1:-/nas3/data/axeyum/harness/dt-array-element/bin/smtcomp_cli-2135}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
C=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/AUFDTLIRA/20200306-Kanig/spark2014bench
NEEDLE='a datatype field sort with no expansion variable'
rc=0
for f in \
  "$C/S702-024__record_attributes_in_allocators__test_constrained.adb_45_22_assert___00.smt2" \
  "$C/P518-021__loop_frame_condition__do_loops.adb_112_22_assert___00.smt2"
do
  b=$(env -u AXEYUM_DT_ARRAY_ELEMENT taskset -c 1 timeout 120 "$AX" "$f" \
        --timeout-ms 24000 --trace 2>&1 | grep -c "$NEEDLE")
  a=$(env AXEYUM_DT_ARRAY_ELEMENT=on taskset -c 1 timeout 120 "$AX" "$f" \
        --timeout-ms 24000 --trace 2>&1 | grep -c "$NEEDLE")
  verdict=LIVE
  if [ "$b" -eq 0 ] || [ "$a" -ne 0 ]; then verdict=NOT-LIVE; rc=1; fi
  printf '%-70s base_refusals=%s arm_refusals=%s %s\n' \
    "$(basename "$f")" "$b" "$a" "$verdict"
done
if [ "$rc" -eq 0 ]; then
  echo "ARM IS LIVE: the ON arm removes the W1 refusal on every probed file"
else
  echo "ARM LIVENESS NOT ESTABLISHED -- do not read an all-agreeing A/B as a null result"
fi
exit "$rc"
