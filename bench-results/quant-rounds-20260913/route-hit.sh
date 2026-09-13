#!/usr/bin/env bash
# Does the route this lane's lever governs actually RUN on this population?
#
# ADR-1945's lane found `ufbv_online` fires on 0 of 400 of its control files,
# so half its control could not have detected anything.  A control set that
# never reaches the code under test measures nothing and reports green, which
# is the worst of both.
#
# The instrument is the route trail, not the verdict: `q:egraph` appears in
# `; route-trail` whenever the e-graph instantiation refuter was ATTEMPTED,
# whatever it then did.  `emat` counts rows whose give-up detail came out of
# the instantiation loop at all (the loop also reports through `q:mbqi-quick`,
# `q:mbqi` and `q:uf-fmf-full`, which share its give-up).
#
# Usage: route-hit.sh <tag> <list> <out.tsv> <core>
set -u
BUDGET=24
HEADROOM=16
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"
AX="${AX:-/nas3/data/axeyum/harness/quant-rounds/bin/smtcomp_cli}"
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }

printf 'file\tverdict\twall_ms\tegraph_rung\temat_giveup\n' > "$OUT"
while read -r f; do
  t0=$(date +%s%N)
  raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>/dev/null)
  t1=$(date +%s%N)
  wall=$(( (t1 - t0) / 1000000 ))
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  if printf '%s\n' "$raw" | grep -q '"route":"q:egraph"'; then eg=yes; else eg=no; fi
  if printf '%s\n' "$raw" | grep -q 'e-matching instantiation'; then em=yes; else em=no; fi
  printf '%s\t%s\t%s\t%s\t%s\n' "${f#"$CORPUS"}" "${v:-none}" "$wall" "$eg" "$em" >> "$OUT"
done < "$LIST"
echo "ROUTE-HIT-DONE $TAG $(($(wc -l < "$OUT") - 1)) rows"
