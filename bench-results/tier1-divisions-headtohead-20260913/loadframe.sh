#!/usr/bin/env bash
# Sample each board host's 1-minute load and the count of FOREIGN taskset pins
# (pins that are not one of this lane's two) every 30 s, for the life of the
# board run.  A board row measured under another lane's load is not wrong -- the
# per-file interleaving is what the comparison rests on -- but the ABSOLUTE
# counts are depressed by it, and a reader cannot tell unless the frame is
# recorded.  This is that record.
#
# It EARNED that on this lane's first launch: it reported 3-4 foreign pins
# within two minutes, and `ps -eo args` named two concurrent lanes pinned to
# logical 0, 2 and 4.  Logical 0 and 2 are the same PHYSICAL cores as this
# board's original 0,8 and 2,10 pins, so the run was stopped and repinned to
# cores 5 and 6 before any row was kept.  A foreign-pin count is not decoration.
OUT=/nas3/data/axeyum/harness/tier1-divisions/out/loadframe.tsv
printf 'ts\thost\tload1\tforeign_pins\n' > "$OUT"
while true; do
  for h in s5 s6 s7; do
    r=$(ssh -o BatchMode=yes -o ConnectTimeout=5 "$h" \
        'cut -d" " -f1 /proc/loadavg; ps -eo args | grep -oE "taskset -c [0-9,-]+" | grep -vcE "taskset -c (5,13|6,14)$" || true' 2>/dev/null | tr "\n" " ")
    printf '%s\t%s\t%s\n' "$(date +%H:%M:%S)" "$h" "$r" >> "$OUT"
  done
  n=$(grep -l 'SHARD-DONE' /nas3/data/axeyum/harness/tier1-divisions/out/*.log 2>/dev/null | wc -l)
  [ "$n" -ge 14 ] && exit 0
  sleep 30
done
