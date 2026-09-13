#!/usr/bin/env bash
# Sample each board host's 1-minute load, the count of FOREIGN taskset pins, and
# -- the column that carries this lane's actual claim -- WHICH cores those
# foreign pins hold, every 30 s for the life of the board run.
#
# A board row measured under another lane's load is not wrong: the per-file
# interleaving is what the comparison rests on, and ambient drift cancels in the
# DIFFERENCE between solvers.  It does not cancel in the ABSOLUTE counts, and
# the absolute counts are this lane's whole deliverable -- it exists to confirm
# or refute seven probe rates.  So what must be recorded is not "was the box
# busy" but "did anything else run on THIS BOARD'S CORES".
#
# A COUNT alone cannot answer that, and this lane learned it the expensive way.
# The first launch used board-six's pins 0,8 and 2,10.  This sampler reported
# 3-4 foreign pins within two minutes and `ps -eo args` named them: a concurrent
# `quant-rounds` lane on logical 0 and 2, and a `nested-array-ir` lane on
# logical 4.  Logical 0 and 2 are the SAME PHYSICAL CORES as 0,8 and 2,10, so
# both shards were sharing a core with another lane's solver.  The run was
# stopped, its partial output deleted, and the board relaunched on cores 5
# and 6.  The foreign pins did not go away -- they are still 3-4 -- so on the
# repinned run the count says nothing and only `foreign_cores` does.
#
# Columns: ts, host, load1, foreign_pin_count, foreign_cores (';'-joined pin
# SPECS, sorted and deduplicated -- ';' because a spec may itself contain a
# comma, e.g. `5,13`).  `OVERLAP` is appended when any foreign pin names a
# logical CPU this board is using (5, 13, 6 or 14), which is the condition that
# would invalidate the absolute counts.
OUT=/nas3/data/axeyum/harness/tier1-divisions/out/loadframe.tsv
MINE='5,13|6,14'
printf 'ts\thost\tload1\tforeign_pins\tforeign_cores\toverlap\n' > "$OUT"
while true; do
  for h in s5 s6 s7; do
    load=$(ssh -o BatchMode=yes -o ConnectTimeout=5 "$h" \
           'cut -d" " -f1 /proc/loadavg' 2>/dev/null)
    pins=$(ssh -o BatchMode=yes -o ConnectTimeout=5 "$h" \
           'ps -eo args | grep -oE "taskset -c [0-9,-]+" | sed "s/taskset -c //" | sort -u' \
           2>/dev/null | grep -vxE "$MINE" | paste -sd';' -)
    n=$(printf '%s' "$pins" | tr ';' '\n' | grep -c . )
    # OVERLAP iff a foreign pin set contains one of this board's logical CPUs.
    # Specs are joined with ';' so a multi-CPU spec like `5,13` stays one token.
    ov=ok
    for spec in $(printf '%s' "$pins" | tr ';' ' '); do
      # >>> overlap-classifier  (controls/loadframe-overlap-control.sh EXTRACTS
      # the lines between these markers and runs THEM, rather than a re-typed
      # copy.  A control that re-implements its subject passes while the
      # shipped code is broken; this one cannot.)
      case "$spec" in
        # A RANGE spec (`0-7`) cannot be tested by membership and may well
        # cover 5 or 6.  Flag it rather than let it read as clear: the wrong
        # direction here is a silent false ok, which is the failure mode this
        # column exists to prevent.
        *-*) ov=OVERLAP ;;
      esac
      case ",$spec," in
        *,5,*|*,13,*|*,6,*|*,14,*) ov=OVERLAP ;;
      esac
      # <<< overlap-classifier
    done
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
      "$(date +%H:%M:%S)" "$h" "${load:-na}" "$n" "${pins:--}" "$ov" >> "$OUT"
  done
  n=$(grep -l 'SHARD-DONE' /nas3/data/axeyum/harness/tier1-divisions/out/*.log 2>/dev/null | wc -l)
  [ "$n" -ge 14 ] && exit 0
  sleep 30
done
