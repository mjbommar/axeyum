#!/usr/bin/env bash
# LRA-TRACE: the ATOM-SCREEN lever's A/B -- ONE BINARY, TWO ENV VALUES.
#
# Arms: `AXEYUM_LRA_ATOM_SCREEN` unset/1 (the shipped allowance, byte-identical)
# against a multiplier, on the same binary.  A wrapper-script pair would be the
# other way to do this; the env is set here instead so the BINARY in both arms is
# provably the same file and the only difference is the value, which is what
# "one binary, two env values" is supposed to buy.
#
# # The arm is proved live by MECHANISM, not by trust
#
# `smtcomp_cli --trace` prints a `; config` line that is FORMATTED FROM the
# environment, so the capture itself carries which arm produced it
# (`env:AXEYUM_LRA_ATOM_SCREEN=...`).  This script keeps both captures and checks
# that line, and REFUSES the whole run if the two arms' config digests are equal
# -- two identical arms produce a perfect zero that looks exactly like agreement,
# and this lane has already shipped one inert lever whose A/B would have printed
# `net +0` for that reason.
#
# # The named controls are not optional
#
# `ad2b40370` recorded THREE falsified cost models for this screen; the third
# bounded Fourier-Motzkin's own allocations correctly and still let
# `QF_LRA/miplib/danoint-266.smt2` reach 7.8 GB with `simplex_rows=n/a` -- the
# simplex engine did not exist, so those bytes were never the tableau and the
# sparse tableau cannot have removed them.  So the two files that defined the
# problem are APPENDED to whatever list the caller passes, and their rows are
# marked `CONTROL` in the output.  A run that decides more rows while aborting a
# control has not earned anything.
#
# EXIT STATUS is a column, never folded into the verdict: ADR-2045 measured
# `losses=0` by verdict with five new ABORTS underneath it.
#
# Usage: screen-ab.sh <tag> <list> <out.tsv> <cores> <bin> <multiplier> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX="$5"; MULT="$6"; BUDGET="${7:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

CONTROLS="QF_LRA/miplib/danoint-266.smt2
QF_LRA/2017-Heizmann-UltimateInvariantSynthesis/_sanfoundry_10_ground.i_6_3_3.bpl_13.smt2"

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }
[ -r "$LIST" ] || { echo "ABORT $TAG: $LIST unreadable"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT non-empty; refusing to overwrite"; exit 2; }
case "$MULT" in ''|*[!0-9]*) echo "ABORT $TAG: multiplier '$MULT' is not a number"; exit 2 ;; esac
[ "$MULT" -le 1 ] && { echo "ABORT $TAG: multiplier $MULT does not move the screen; both arms would be the shipped one"; exit 2; }

OUTDIR="$(dirname -- "$OUT")/screencaps-$TAG"
mkdir -p "$OUTDIR" || exit 2

run_arm() {  # $1 = multiplier value, $2 = capture path; prints verdict\tms\trc
  local t0 t1 rc v
  t0=$(date +%s%N)
  AXEYUM_LRA_ATOM_SCREEN="$1" timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
    bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
    "$AX" "$f" > "$2" 2>/dev/null
  rc=$?
  t1=$(date +%s%N)
  v=$(grep -m1 -oE '^(sat|unsat|unknown)$' -- "$2" 2>/dev/null || true)
  printf '%s\t%s\t%s' "${v:-none}" "$(( (t1 - t0) / 1000000 ))" "$rc"
}

# Population: the caller's list, plus the two named controls if absent from it.
POP="$OUTDIR/population.txt"
cp -- "$LIST" "$POP"
while IFS= read -r c; do
  [ -z "$c" ] && continue
  grep -qxF -- "$c" "$POP" || printf '%s\n' "$c" >> "$POP"
done <<EOF
$CONTROLS
EOF

printf 'file\tA\tA_ms\tA_rc\tB\tB_ms\tB_rc\tfirst\tstatus\tcontrol\n' > "$OUT"
n=0
checked_live=0
while read -r rel; do
  [ -z "$rel" ] && continue
  f="$CORPUS$rel"
  [ -r "$f" ] || { echo "UNREADABLE $rel" >&2; continue; }
  n=$((n + 1))
  slug="$(printf '%s' "$rel" | tr '/' '_')"
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  is_control=no
  printf '%s\n' "$CONTROLS" | grep -qxF -- "$rel" && is_control=CONTROL
  if [ $((n % 2)) -eq 1 ]; then
    first=A; a=$(run_arm 1 "$OUTDIR/$slug.A.out"); b=$(run_arm "$MULT" "$OUTDIR/$slug.B.out")
  else
    first=B; b=$(run_arm "$MULT" "$OUTDIR/$slug.B.out"); a=$(run_arm 1 "$OUTDIR/$slug.A.out")
  fi
  # MECHANISM check, once: the `; config` line is formatted from the env, so if
  # the two arms' digests match, the lever did not reach the binary and every
  # number below is vacuous.
  if [ "$checked_live" -eq 0 ]; then
    da=$(grep -m1 -oE '; config digest=[0-9a-f]+' -- "$OUTDIR/$slug.A.out" 2>/dev/null || true)
    db=$(grep -m1 -oE '; config digest=[0-9a-f]+' -- "$OUTDIR/$slug.B.out" 2>/dev/null || true)
    if [ -n "$da" ] && [ "$da" = "$db" ]; then
      echo "ABORT $TAG: both arms produced the SAME config digest ($da)."
      echo "  The lever did not reach the binary; every number in this run would"
      echo "  be a perfect zero that looks exactly like agreement."
      exit 2
    fi
    checked_live=1
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$rel" "$a" "$b" "$first" "${st:-none}" "$is_control" >> "$OUT"
done < "$POP"
echo "SCREEN-AB-DONE $TAG $n files (multiplier $MULT) -> $OUT"
