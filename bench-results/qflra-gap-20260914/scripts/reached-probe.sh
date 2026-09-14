#!/usr/bin/env bash
# Did the lever REACH the rung, or reach it and come out the other side?
#
# ADR-2030's distinction, applied here.  The census says 24 undecided rows were
# refused by the online CDCL(T) LRA ADMISSION SCREEN (`online_probe=
# admission-screen`) and then spent the whole budget in the offline dense
# engine.  `AXEYUM_MEMORY_LIMIT_MB=8192` raises that screen's budget 12.8x.
#
# Three outcomes are possible and a verdict count cannot tell them apart:
#   admission-screen  -> the lever did NOT reach: still refused
#   took              -> reached, engine ran, and it DECIDED
#   model-did-not-replay / timeout -> reached, ran, and could not finish
#
# The screen reports on itself in `; lazy-smt ... online_probe=`, so this reads
# the mechanism rather than inferring it.
#
# Usage: reached-probe.sh <list> <out.tsv> <cores> <arm_mb>
set -u
LIST="$1"; OUT="$2"; PIN="$3"; ARM="$4"
BIN=/nas3/data/axeyum/harness/qflra-gap/bin/smtcomp_cli-cfcae7fa7
VLIM=$((8 * 1024 * 1024))

printf 'file\tarm\tprobe_base\tprobe_arm\tverdict_base\tverdict_arm\tatoms_arm\n' > "$OUT"
while read -r f; do
  [ -z "$f" ] && continue
  ob=$( ( ulimit -v $VLIM; timeout 45 taskset -c "$PIN" "$BIN" "$f" --timeout-ms 24000 --trace ) 2>/dev/null )
  oa=$( ( ulimit -v $VLIM; AXEYUM_MEMORY_LIMIT_MB="$ARM" timeout 45 taskset -c "$PIN" "$BIN" "$f" --timeout-ms 24000 --trace ) 2>/dev/null )
  pb=$(printf '%s\n' "$ob" | grep -m1 -oE 'online_probe=[a-z-]+' | cut -d= -f2)
  pa=$(printf '%s\n' "$oa" | grep -m1 -oE 'online_probe=[a-z-]+' | cut -d= -f2)
  vb=$(printf '%s\n' "$ob" | grep -m1 -oE '^(sat|unsat|unknown)$')
  va=$(printf '%s\n' "$oa" | grep -m1 -oE '^(sat|unsat|unknown)$')
  aa=$(printf '%s\n' "$oa" | grep -m1 -oE ' atoms=[0-9]+' | cut -d= -f2)
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$ARM" \
    "${pb:-NONE}" "${pa:-NONE}" "${vb:-none}" "${va:-none}" "${aa:-NONE}" >> "$OUT"
done < "$LIST"
echo "REACHED_COMPLETE rows=$(( $(wc -l < "$OUT") - 1 ))"
