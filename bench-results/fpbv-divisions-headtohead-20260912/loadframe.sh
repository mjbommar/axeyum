#!/usr/bin/env bash
# Sample each board host's 1-minute load and the count of FOREIGN taskset pins
# (pins that are not one of this lane's two) every 30 s, for the life of the
# board run.  A board row measured under another lane's load is not wrong -- the
# per-file interleaving is what the comparison rests on -- but the ABSOLUTE
# counts are depressed by it, and a reader cannot tell unless the frame is
# recorded.  This is that record.
OUT=/nas3/data/axeyum/harness/fpbv-divisions/out/loadframe.tsv
printf 'ts\thost\tload1\tforeign_pins\n' > "$OUT"
while true; do
  for h in s5 s6 s7; do
    r=$(ssh -o BatchMode=yes -o ConnectTimeout=5 "$h" \
        'cut -d" " -f1 /proc/loadavg; ps -eo args | grep -oE "taskset -c [0-9,-]+" | grep -vcE "taskset -c (0,8|2,10)$" || true' 2>/dev/null | tr "\n" " ")
    printf '%s\t%s\t%s\n' "$(date +%H:%M:%S)" "$h" "$r" >> "$OUT"
  done
  grep -l 'SHARD-DONE' /nas3/data/axeyum/harness/fpbv-divisions/out/*.log 2>/dev/null \
    | wc -l | grep -q '^6$' && exit 0
  sleep 30
done
