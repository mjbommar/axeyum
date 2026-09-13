#!/usr/bin/env bash
# One shard of the fair head-to-head for the four A-divisions.
#
# Protocol copied from bench-results/six-divisions-headtohead-20260912/shard-run.sh
# (lane BOARD-SIX, ADR-1941).  Two changes, both so this lane can run an A/B:
#
#   * the axeyum binary comes from $AX_BIN, so arm A and arm B are two paths to
#     two binaries rather than two checkouts;
#   * $ARMS selects which solvers run.  The baseline pass runs all three; the
#     A/B pass over the SAME files runs `axeyum` only twice, one binary per arm,
#     back to back on one file before either moves on -- the same
#     interleave-per-file rule, applied to the two arms instead of the three
#     solvers, because that is what makes ambient load cancel in the difference.
#
# UNITS DIFFER AND MIXING THEM SILENTLY CORRUPTS A BOARD:
#   z3   -T:<SECONDS>          cvc5  --tlimit=<MILLISECONDS>
#
# Usage: AX_BIN=<path> [AX_BIN_B=<path>] shard-run.sh <tag> <list> <out.tsv> <core>
set -u
BUDGET=24            # board protocol: 24 s wall, 8 GiB address space
HEADROOM=16          # wrapper timeout = BUDGET + HEADROOM
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"
AX="${AX_BIN:?AX_BIN must name the axeyum binary}"
AXB="${AX_BIN_B:-}"
Z3=/usr/bin/z3
CVC5=/nas3/data/axeyum/harness/bin/cvc5
VLIM=$((8 * 1024 * 1024))   # ulimit -v is KiB -> 8 GiB
ARMS="${ARMS:-axeyum z3 cvc5}"

for b in $ARMS; do
  case "$b" in
    axeyum) p="$AX" ;; axeyumb) p="$AXB" ;; z3) p="$Z3" ;; cvc5) p="$CVC5" ;;
    *) echo "ABORT $TAG: unknown arm $b"; exit 2 ;;
  esac
  [ -x "$p" ] || { echo "ABORT $TAG: $b binary '$p' missing or not executable"; exit 2; }
done

run() { # $1 solver  $2 file -> "verdict<TAB>seconds<TAB>flag"
  local t0 t1 raw rc v k
  t0=$(date +%s.%N)
  case "$1" in
    axeyum)  raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
               bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
               "$AX" "$2" 2>/dev/null) ;;
    axeyumb) raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
               bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
               "$AXB" "$2" 2>/dev/null) ;;
    z3)      raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
               bash -c "ulimit -v $VLIM; exec \"\$0\" -T:$BUDGET \"\$1\"" \
               "$Z3" "$2" 2>/dev/null) ;;
    cvc5)    raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
               bash -c "ulimit -v $VLIM; exec \"\$0\" --tlimit=$((BUDGET * 1000)) \"\$1\"" \
               "$CVC5" "$2" 2>/dev/null) ;;
  esac
  rc=$?
  t1=$(date +%s.%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat)$')
  k=ok
  [ "$rc" = 124 ] && k=wrapper-killed
  [ "$rc" = 134 ] && k=rc134
  [ "$rc" = 137 ] && k=sigkill
  printf '%s\t%.2f\t%s' "${v:-unknown}" "$(echo "$t1-$t0" | bc)" "$k"
}

# The row key is the path RELATIVE TO THE CORPUS ROOT, not the basename:
# basenames COLLIDE across directories in these corpora.
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

# The header names only the arms that ran, so a column can never be read as an
# arm that was skipped.
hdr='file'
for s in $ARMS; do hdr="$hdr	$s	${s}_s	${s}_k"; done
printf '%s\tstatus\n' "$hdr" > "$OUT"

read -r -a ARM_A <<< "$ARMS"
nsolv=${#ARM_A[@]}
i=0
while read -r f; do
  i=$((i + 1))
  # Rotate which arm goes first, so nobody systematically benefits from a cold
  # or warm page cache. Rotation by i % nsolv over the fixed arm array.
  order=()
  for ((j = 0; j < nsolv; j++)); do
    order+=("${ARM_A[$(((i + j) % nsolv))]}")
  done
  declare -A R=()
  for s in "${order[@]}"; do R[$s]=$(run "$s" "$f"); done
  row="${f#"$CORPUS"}"
  for s in $ARMS; do row="$row	${R[$s]}"; done
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' "$f" | awk '{print $2}')
  printf '%s\t%s\n' "$row" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "SHARD-DONE $TAG $(($(wc -l < "$OUT") - 1)) rows"
