#!/usr/bin/env bash
# Report, per host, every PHYSICAL core held by more than one pinned job --
# this lane's jobs included.
#
# This exists because the lane made that mistake twice in one hour.  First it
# launched on board-six's pins 0,8 and 2,10 while a `quant-rounds` lane held
# logical 0 and 2 -- the same physical cores.  Then, after re-balancing, it read
# ONE shard's `CENSUS-DONE` as "the census is finished" and started the FP board
# on cores the other census shard still held.  Both were caught, the affected
# rows deleted and the work relaunched, but neither was caught BY A CHECK: the
# first by reading `ps` on a hunch, the second by noticing a merge came up one
# row short.
#
# `loadframe.sh`'s OVERLAP column cannot cover this.  It asks whether a FOREIGN
# pin touches the board's ORIGINAL two cores, and after the re-balance this lane
# holds eight cores across three boxes -- so its own shards read as "foreign"
# and a self-collision reads as `ok`.  A check has to be about ALL pinned jobs,
# not about a fixed pair.
#
# A Ryzen 7 7840HS is 8 physical cores with SMT siblings at +8, so logical n and
# n+8 are ONE core: `5` and `13` collide, `5` and `6` do not.  Two processes
# sharing ONE pin spec are the same shard's sequential solvers, which is the
# protocol, not a collision.
#
# Exit 1 if any collision is found, so a caller can gate on it.
set -u
# >>> collision-awk  (controls/core-collision-control.sh EXTRACTS this program
# and runs IT over fixtures with known answers, rather than re-typing it.  A
# control that re-implements its subject passes while the shipped one is
# broken.)
AWKPROG='
  { spec = $2
    n = split(spec, cpus, ",")
    for (i = 1; i <= n; i++) {
      core = cpus[i] % 8
      if (!((core SUBSEP spec) in seen)) {
        seen[core SUBSEP spec] = 1
        holders[core] = holders[core] " " spec
      }
    }
  }
  END { bad = 0
        for (c in holders) {
          n = split(holders[c], a, " ")
          # split with a SINGLE SPACE separator is the DEFAULT splitting rule,
          # which strips leading and trailing blanks -- so the leading space in
          # holders[c] does NOT produce an empty first field.  The first version
          # of this line assumed it did and tested n > 2, which needed THREE
          # specs on one core and so reported NO-CORE-COLLISIONS over a live
          # fleet while detecting nothing.  controls/core-collision-control.sh
          # is what caught it; the fleet run did not.
          #
          # NOTE: no apostrophes in this program.  AWKPROG is single-quoted, so
          # one apostrophe ends the string and the script stops parsing --
          # which also happened here, and the control did NOT catch it, because
          # it extracts the program and never runs the subject.  The control
          # now runs bash -n on the subject first.
          if (n > 1) {
            printf "%s: PHYSICAL CORE %s held by:%s\n", host, c, holders[c]
            bad = 1
          }
        }
        exit bad }'
# <<< collision-awk
HOSTS="${*:-s5 s6 s7}"
bad=0
for h in $HOSTS; do
  out=$(ssh -o BatchMode=yes -o ConnectTimeout=5 "$h" \
    'ps -eo args | grep -oE "taskset -c [0-9,]+" | sed "s/taskset -c //" | sort | uniq -c' \
    2>/dev/null)
  [ -n "$out" ] || { echo "$h: no pinned jobs (or unreachable)"; continue; }
  printf '%s\n' "$out" | awk -v host="$h" "$AWKPROG" || bad=1
done
[ "$bad" = 0 ] && echo "NO-CORE-COLLISIONS on: $HOSTS"
exit "$bad"
