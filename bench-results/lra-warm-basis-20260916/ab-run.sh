#!/usr/bin/env bash
# ADR-2125 A/B: ONE binary, TWO values of `AXEYUM_LRA_WARM_CUBE`.
#
# # The vacuity guard, and why it is where it is
#
# ADR-2100's runner refuses unless its two BINARIES hash differently, because two
# identical arms produce a perfect zero that looks exactly like agreement. This
# change is a lever, so the same risk lives somewhere else: two arms that differ
# only in an environment variable the binary never READS are equally vacuous and
# equally invisible. `--mechanism-check` is that guard here.
#
# This lane needed it. Its FIRST mechanism check read `warm_cube_checks=0` in
# BOTH arms: the warm engine was refused by `MAX_TABLEAU_CELLS`, a DENSE-CELL cap
# on a tableau that has stored nonzeros since ADR-2111, and the A/B would have
# printed `net +0` from an arm that never ran -- the exact reading ADR-2111 had
# to publish about its own `TableauReserve`. Do not skip it.
#
# Arms run BACK TO BACK on the same file on the same pinned core, with the arm
# ORDER alternating per file, so ambient load cancels in the DIFFERENCE rather
# than landing on whichever arm ran second.
#
# Usage: ab-run.sh <tag> <list> <out.tsv> <cores> <bin> [budget_s]
#        ab-run.sh --mechanism-check <file> <cores> <bin>
set -u

CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/
HEADROOM=16
VLIM=$((8 * 1024 * 1024))

field() {
  sed -n "s/^; $2 .*/&/p" -- "$1" 2>/dev/null | tr ' ' '\n' | sed -n "s/^$3=//p" | head -1
}

run_one() {
  # $1 arm value, $2 file, $3 cores, $4 bin, $5 budget, $6 out-prefix
  AXEYUM_LRA_WARM_CUBE="$1" \
    timeout $(($5 + HEADROOM)) taskset -c "$3" \
    bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $(($5 * 1000))" \
    "$4" "$2" > "$6.out" 2> "$6.err"
  return $?
}

if [ "${1:-}" = "--mechanism-check" ]; then
  F="$2"; PIN="$3"; AX="$4"
  TMP="$(mktemp -d)"
  run_one off "$F" "$PIN" "$AX" 24 "$TMP/a"
  run_one on  "$F" "$PIN" "$AX" 24 "$TMP/b"
  A=$(field "$TMP/a.out" lazy-smt warm_cube_checks)
  B=$(field "$TMP/b.out" lazy-smt warm_cube_checks)
  BUILD=$(field "$TMP/b.out" lazy-smt warm_cube_build)
  echo "mechanism-check: off=${A:-none} on=${B:-none} build=${BUILD:-none}"
  rm -rf "$TMP"
  # The arm must be ZERO in A and NONZERO in B. Absent counts as a failure, not
  # as zero: a row that printed no `; lazy-smt` line says nothing about whether
  # the lever moved the engine, and treating silence as a pass is how an inert
  # arm gets reported as agreement.
  if [ -z "${A:-}" ] || [ -z "${B:-}" ]; then
    echo "MECHANISM-CHECK FAILED: no lazy-smt line on one arm -- this file does not reach the route"
    exit 2
  fi
  if [ "$A" != "0" ] || [ "$B" = "0" ]; then
    echo "MECHANISM-CHECK FAILED: off=$A on=$B build=$BUILD -- the lever does not move the engine on this file"
    exit 2
  fi
  echo "mechanism-check OK: the lever moves the engine on this file"
  exit 0
fi

TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX="$5"; BUDGET="${6:-24}"

[ -x "$AX" ] || { echo "ABORT: $AX missing or not executable"; exit 2; }
[ -r "$LIST" ] || { echo "ABORT: $LIST unreadable"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT non-empty; refusing to overwrite"; exit 2; }

OUTDIR="$(dirname -- "$OUT")/ab-captures-$TAG"
mkdir -p "$OUTDIR" || exit 2

printf 'file\tfirst\ta_rc\ta_ms\ta_verdict\ta_total_ms\tb_rc\tb_ms\tb_verdict\tb_total_ms\tb_warm_build\tb_warm_checks\tb_warm_declines\tb_warm_cold_restarts\ta_cold_builds\tb_cold_builds\tstatus\n' > "$OUT"

n=0
while read -r rel; do
  [ -z "$rel" ] && continue
  f="$CORPUS$rel"
  if [ ! -r "$f" ]; then echo "UNREADABLE $rel" >&2; continue; fi
  slug="$(printf '%s' "$rel" | tr '/' '_')"
  n=$((n + 1))
  # Alternate which arm runs FIRST, per file.
  if [ $((n % 2)) -eq 0 ]; then first="B"; else first="A"; fi

  if [ "$first" = "A" ]; then
    t0=$(date +%s%N); run_one off "$f" "$PIN" "$AX" "$BUDGET" "$OUTDIR/$slug.a"; arc=$?; t1=$(date +%s%N)
    t2=$(date +%s%N); run_one on  "$f" "$PIN" "$AX" "$BUDGET" "$OUTDIR/$slug.b"; brc=$?; t3=$(date +%s%N)
  else
    t2=$(date +%s%N); run_one on  "$f" "$PIN" "$AX" "$BUDGET" "$OUTDIR/$slug.b"; brc=$?; t3=$(date +%s%N)
    t0=$(date +%s%N); run_one off "$f" "$PIN" "$AX" "$BUDGET" "$OUTDIR/$slug.a"; arc=$?; t1=$(date +%s%N)
  fi

  av=$(grep -m1 -oE '^(sat|unsat|unknown)$' -- "$OUTDIR/$slug.a.out" 2>/dev/null || true)
  bv=$(grep -m1 -oE '^(sat|unsat|unknown)$' -- "$OUTDIR/$slug.b.out" 2>/dev/null || true)
  # The declared `:status`, for the soundness column. Absent on many files, which
  # is why the comparable denominator is published beside the count.
  st=$(sed -n 's/.*set-info *:status *\([a-z]*\).*/\1/p' -- "$f" 2>/dev/null | head -1)
  status="${st:-none}"

  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$rel" "$first" \
    "$arc" "$(( (t1 - t0) / 1000000 ))" "${av:-none}" "$(field "$OUTDIR/$slug.a.out" route total_ms)" \
    "$brc" "$(( (t3 - t2) / 1000000 ))" "${bv:-none}" "$(field "$OUTDIR/$slug.b.out" route total_ms)" \
    "$(field "$OUTDIR/$slug.b.out" lazy-smt warm_cube_build)" \
    "$(field "$OUTDIR/$slug.b.out" lazy-smt warm_cube_checks)" \
    "$(field "$OUTDIR/$slug.b.out" lazy-smt warm_cube_declines)" \
    "$(field "$OUTDIR/$slug.b.out" lazy-smt warm_cube_cold_restarts)" \
    "$(field "$OUTDIR/$slug.a.out" lazy-smt simplex_cold_builds)" \
    "$(field "$OUTDIR/$slug.b.out" lazy-smt simplex_cold_builds)" \
    "$status" >> "$OUT"
done < "$LIST"

echo "AB-DONE $TAG $(($(wc -l < "$OUT") - 1)) rows"
