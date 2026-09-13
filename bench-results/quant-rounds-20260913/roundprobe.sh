#!/usr/bin/env bash
# The unambiguous form of the bracket: does the ROUND-CEILING give-up appear
# ANYWHERE in the run?
#
# `exit-census.sh` reads the FIRST give-up line (`grep -m1`), which is the
# convention `board-six`'s census used -- and several ladder rungs run the
# instantiation loop (`q:mbqi-quick`, `q:egraph`, `q:mbqi`, `q:uf-fmf-full`),
# so the first line can belong to a rung that timed out before the loop even
# started.  That is how five AUFLIA rows come back `OTHER` rather than with the
# loop's own exit, and it makes "the first give-up was not ROUND" a weaker claim
# than it looks.
#
# This scans the WHOLE trace instead.  `round=yes` means some rung in this
# dispatch ran the instantiation loop to its ceiling; `round=no` means no rung
# did, whatever any single line says.  A `no` here cannot be a reporting
# artifact.
#
# Usage: roundprobe.sh <tag> <list> <out.tsv> <core> [VAR=VAL ...]
set -u
BUDGET=24
HEADROOM=16
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; shift 4
AX="${AX:-/nas3/data/axeyum/harness/quant-rounds/bin/smtcomp_cli}"
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }

printf 'file\tverdict\tround_anywhere\tfixpoint_anywhere\theadroom_anywhere\tgiveup_lines\n' > "$OUT"
while read -r f; do
  raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          env "$@" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>/dev/null)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  # Counts, not a boolean: a run whose trail carries the string twenty times and
  # one that carries it once are the same finding here, but a ZERO has to be a
  # real zero rather than a grep that never saw the subject -- so the total
  # give-up count is printed beside it as the coverage control. A row with 0
  # give-up lines AND 0 round hits is UNMEASURED, not a negative.
  r=$(printf '%s\n' "$raw" | grep -c 'did not refute within the round budget')
  x=$(printf '%s\n' "$raw" | grep -c 'reached fixpoint without refuting after')
  h=$(printf '%s\n' "$raw" | grep -c 'could not fit another round with growth headroom')
  g=$(printf '%s\n' "$raw" | grep -c 'give-up kind=')
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "${f#"$CORPUS"}" "${v:-none}" "$r" "$x" "$h" "$g" >> "$OUT"
done < "$LIST"
echo "ROUNDPROBE-DONE $TAG $(($(wc -l < "$OUT") - 1)) rows"
