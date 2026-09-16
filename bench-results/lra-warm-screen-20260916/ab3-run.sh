#!/usr/bin/env bash
# ADR-2132 A/B: ONE binary, THREE values of `AXEYUM_LRA_WARM_CUBE`.
#
# # Why three arms and not two
#
# The screen's whole claim is comparative: that it keeps [ADR-2125]'s gain
# WITHOUT its losses.  An `off` vs `screened` pair can say the screened arm is
# net +0; it cannot say whether that is because the screen worked or because the
# lever never did anything on this population.  `on` is the reference that tells
# those apart, and it is the arm ADR-2125 measured, so the two lanes' numbers sit
# in one table rather than across two documents on two days.
#
# The three arms run BACK TO BACK on the same file on the same pinned core, and
# the ORDER ROTATES per file (three rotations, not two), so no arm systematically
# gets the warm page cache or the cold one.
#
# # The vacuity guard
#
# [ADR-2100]'s runner refuses unless its two BINARIES hash differently, because
# two identical arms give a perfect zero that looks exactly like agreement.  With
# one binary the risk moves to "the binary never reads the variable", and
# ADR-2125 PROVED that risk is real here: its first mechanism check read
# `warm_cube_checks=0` in BOTH arms because a dense-cell cap refused a sparse
# tableau.  `--mechanism-check` is that guard, and it now checks the SCREENED arm
# too -- which has its own way of being inert that `on` does not: the file can
# simply never cross the threshold.
#
# # AXEYUM_AB3_ARMS: which arms to run
#
# `ABC` (the default) is the three-arm form the ship decision rests on. `AC` runs
# only `off` and `screened`, which is what the EXPOSURE divisions need: their
# question is "did the screen regress a division it was not aimed at", and that
# is answered by the pair. Dropping `on` there is a deliberate spend of compute
# on the populations the decision rests on, and the omitted arm's columns are
# written EMPTY rather than as zeros -- an arm that did not run reports nothing,
# not that it answered nothing, which is the distinction ADR-2125's `20 SILENT`
# rows exist to keep.
#
# Usage: ab3-run.sh <tag> <list> <out.tsv> <cores> <bin> [budget_s]
#        ab3-run.sh --mechanism-check <file> <cores> <bin>
set -u
ARMS="${AXEYUM_AB3_ARMS:-ABC}"
case "$ARMS" in
  ABC|AC) ;;
  *) echo "ABORT: AXEYUM_AB3_ARMS must be ABC or AC, got '$ARMS'"; exit 2 ;;
esac

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
  run_one off      "$F" "$PIN" "$AX" 24 "$TMP/a"
  run_one on       "$F" "$PIN" "$AX" 24 "$TMP/b"
  run_one screened "$F" "$PIN" "$AX" 24 "$TMP/c"
  A=$(field "$TMP/a.out" lazy-smt warm_cube_checks)
  B=$(field "$TMP/b.out" lazy-smt warm_cube_checks)
  C=$(field "$TMP/c.out" lazy-smt warm_cube_checks)
  BB=$(field "$TMP/b.out" lazy-smt warm_cube_build)
  CB=$(field "$TMP/c.out" lazy-smt warm_cube_build)
  AC=$(field "$TMP/a.out" lazy-smt simplex_cold_builds)
  echo "mechanism-check: off=${A:-none}/${AC:-none} on=${B:-none}/${BB:-none} screened=${C:-none}/${CB:-none}"
  rm -rf "$TMP"
  # Absent counts as a failure, not as zero: a row that printed no `; lazy-smt`
  # line says nothing about whether the lever moved the engine, and treating
  # silence as a pass is how an inert arm gets reported as agreement.
  if [ -z "${A:-}" ] || [ -z "${B:-}" ] || [ -z "${C:-}" ]; then
    echo "MECHANISM-CHECK FAILED: no lazy-smt line on some arm -- this file does not reach the route"
    exit 2
  fi
  if [ "$A" != "0" ]; then
    echo "MECHANISM-CHECK FAILED: off=$A -- the `off` arm ran the warm decider"
    exit 2
  fi
  if [ "$B" = "0" ]; then
    echo "MECHANISM-CHECK FAILED: on=$B build=$BB -- the lever does not move the engine on this file"
    exit 2
  fi
  if [ "$C" = "0" ]; then
    echo "MECHANISM-CHECK FAILED: screened=$C build=$CB cold_builds(off)=$AC -- the SCREEN never opened on this file"
    exit 2
  fi
  echo "mechanism-check OK: all three arms distinguishable on this file"
  exit 0
fi

TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX="$5"; BUDGET="${6:-24}"

[ -x "$AX" ] || { echo "ABORT: $AX missing or not executable"; exit 2; }
[ -r "$LIST" ] || { echo "ABORT: $LIST unreadable"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT non-empty; refusing to overwrite"; exit 2; }

OUTDIR="$(dirname -- "$OUT")/ab3-captures-$TAG"
mkdir -p "$OUTDIR" || exit 2

printf 'file\torder\ta_rc\ta_ms\ta_verdict\ta_total_ms\tb_rc\tb_ms\tb_verdict\tb_total_ms\tc_rc\tc_ms\tc_verdict\tc_total_ms\ta_cold_builds\tb_cold_builds\tc_cold_builds\ta_cube_collect_ms\ta_cube_simplex_ms\tb_cube_collect_ms\tb_cube_simplex_ms\tb_warm_solve_ms\tb_warm_sync_ms\tb_warm_checks\tb_warm_build\tb_warm_restarts\tb_warm_fill_peak\tc_cube_collect_ms\tc_cube_simplex_ms\tc_warm_solve_ms\tc_warm_sync_ms\tc_warm_checks\tc_warm_build\tc_warm_restarts\tc_warm_fill_peak\tstatus\n' > "$OUT"

n=0
while read -r rel; do
  [ -z "$rel" ] && continue
  f="$CORPUS$rel"
  if [ ! -r "$f" ]; then echo "UNREADABLE $rel" >&2; continue; fi
  slug="$(printf '%s' "$rel" | tr '/' '_')"
  n=$((n + 1))
  # Rotations, so each arm is first on an equal share of the rows.
  if [ "$ARMS" = "AC" ]; then
    case $((n % 2)) in
      1) order="AC" ;;
      *) order="CA" ;;
    esac
  else
    case $((n % 3)) in
      1) order="ABC" ;;
      2) order="BCA" ;;
      *) order="CAB" ;;
    esac
  fi

  # EMPTY, not zero, for an arm this run does not have. `0` would read as
  # "it exited cleanly in no time" and `none` as "it ran and decided
  # nothing"; both are claims about an arm that never started. Only a
  # rotation letter below replaces them.
  a_ms=""; b_ms=""; c_ms=""; arc=""; brc=""; crc=""
  for arm in $(printf '%s' "$order" | fold -w1); do
    case "$arm" in
      A) t0=$(date +%s%N); run_one off      "$f" "$PIN" "$AX" "$BUDGET" "$OUTDIR/$slug.a"; arc=$?
         a_ms=$(( ($(date +%s%N) - t0) / 1000000 )) ;;
      B) t0=$(date +%s%N); run_one on       "$f" "$PIN" "$AX" "$BUDGET" "$OUTDIR/$slug.b"; brc=$?
         b_ms=$(( ($(date +%s%N) - t0) / 1000000 )) ;;
      C) t0=$(date +%s%N); run_one screened "$f" "$PIN" "$AX" "$BUDGET" "$OUTDIR/$slug.c"; crc=$?
         c_ms=$(( ($(date +%s%N) - t0) / 1000000 )) ;;
    esac
  done

  # An arm that did not run leaves no capture, so `field` prints the empty
  # string and every one of its columns is EMPTY. The summarizer reads that as
  # "did not run" and puts the row in no denominator of that arm's table.
  verdict_of() {  # $1 = capture prefix, $2 = that arm's rc (EMPTY if it did not run)
    if [ -z "$2" ]; then printf ''; return; fi
    v=$(grep -m1 -oE '^(sat|unsat|unknown)$' -- "$1.out" 2>/dev/null || true)
    printf '%s' "${v:-none}"
  }
  av=$(verdict_of "$OUTDIR/$slug.a" "$arc")
  bv=$(verdict_of "$OUTDIR/$slug.b" "$brc")
  cv=$(verdict_of "$OUTDIR/$slug.c" "$crc")
  # The declared `:status`, for the soundness column. Absent on many files, which
  # is why the comparable denominator is published beside the count.
  st=$(sed -n 's/.*set-info *:status *\([a-z]*\).*/\1/p' -- "$f" 2>/dev/null | head -1)

  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$rel" "$order" \
    "$arc" "$a_ms" "$av" "$(field "$OUTDIR/$slug.a.out" route total_ms)" \
    "$brc" "$b_ms" "$bv" "$(field "$OUTDIR/$slug.b.out" route total_ms)" \
    "$crc" "$c_ms" "$cv" "$(field "$OUTDIR/$slug.c.out" route total_ms)" \
    "$(field "$OUTDIR/$slug.a.out" lazy-smt simplex_cold_builds)" \
    "$(field "$OUTDIR/$slug.b.out" lazy-smt simplex_cold_builds)" \
    "$(field "$OUTDIR/$slug.c.out" lazy-smt simplex_cold_builds)" \
    "$(field "$OUTDIR/$slug.a.out" lazy-smt cube_collect_ms)" \
    "$(field "$OUTDIR/$slug.a.out" lazy-smt cube_simplex_ms)" \
    "$(field "$OUTDIR/$slug.b.out" lazy-smt cube_collect_ms)" \
    "$(field "$OUTDIR/$slug.b.out" lazy-smt cube_simplex_ms)" \
    "$(field "$OUTDIR/$slug.b.out" lazy-smt warm_cube_solve_ms)" \
    "$(field "$OUTDIR/$slug.b.out" lazy-smt warm_cube_sync_ms)" \
    "$(field "$OUTDIR/$slug.b.out" lazy-smt warm_cube_checks)" \
    "$(field "$OUTDIR/$slug.b.out" lazy-smt warm_cube_build)" \
    "$(field "$OUTDIR/$slug.b.out" lazy-smt warm_cube_cold_restarts)" \
    "$(field "$OUTDIR/$slug.b.out" lazy-smt warm_cube_fill_peak)" \
    "$(field "$OUTDIR/$slug.c.out" lazy-smt cube_collect_ms)" \
    "$(field "$OUTDIR/$slug.c.out" lazy-smt cube_simplex_ms)" \
    "$(field "$OUTDIR/$slug.c.out" lazy-smt warm_cube_solve_ms)" \
    "$(field "$OUTDIR/$slug.c.out" lazy-smt warm_cube_sync_ms)" \
    "$(field "$OUTDIR/$slug.c.out" lazy-smt warm_cube_checks)" \
    "$(field "$OUTDIR/$slug.c.out" lazy-smt warm_cube_build)" \
    "$(field "$OUTDIR/$slug.c.out" lazy-smt warm_cube_cold_restarts)" \
    "$(field "$OUTDIR/$slug.c.out" lazy-smt warm_cube_fill_peak)" \
    "${st:-none}" >> "$OUT"
done < "$LIST"

echo "AB3-DONE $TAG $(($(wc -l < "$OUT") - 1)) rows"
