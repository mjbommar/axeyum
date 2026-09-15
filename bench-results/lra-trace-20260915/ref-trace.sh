#!/usr/bin/env bash
# LRA-TRACE: run the SAME 93 files through z3's TWO arithmetic solvers and
# through cvc5, under the SAME envelope our own census used.
#
# # Why two z3 arms and not one
#
# `smt.arith.solver` selects which arithmetic theory z3 builds
# (`src/params/theory_arith_params.h:25-32`):
#
#   2 = AS_OLD_ARITH  -> `theory_mi_arith`, the classic dense-ish simplex
#   6 = AS_NEW_ARITH  -> `theory_lra` over `lp::lar_solver`, the DEFAULT for
#                        QF_LRA (`src/params/smt_params_helper.pyg:65`)
#
# Our engine is a Dutertre-de Moura simplex, which is what BOTH of those are by
# name.  So "z3 decides 166 and we decide 107" cannot, on its own, say whether
# the gap is the ALGORITHM or the IMPLEMENTATION.  Running both arms separates
# them: a file that solver 2 and solver 6 both decide is not being decided by
# `lar_solver`'s data structures, and a file only solver 6 decides is.
#
# # The envelope is OURS, deliberately
#
# 24 s / 8 GiB / one pinned core pair, identical to `trace-census.sh`, so the
# columns are comparable to our own row.  `-st` is z3's statistics block and
# `--stats` is cvc5's; both go to stdout with the verdict, and both are kept
# whole rather than grepped for one token -- the repository's own measured
# harness defect (ADR-2102) was three sweeps that computed a full capture and
# threw it away.
#
# A reference's non-zero exit is DATA, not this script's failure.
#
# Usage: ref-trace.sh <shard-id> <list> <out.tsv> <cores> [budget_s]
set -u
SHARD="$1"; LIST="$2"; OUT="$3"; PIN="$4"; BUDGET="${5:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/
Z3="${Z3:-/usr/bin/z3}"
CVC5="${CVC5:-/nas3/data/axeyum/harness/bin/cvc5}"

[ -x "$Z3" ] || { echo "ABORT: $Z3 missing"; exit 2; }
[ -r "$LIST" ] || { echo "ABORT: $LIST unreadable"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT non-empty; refusing to overwrite"; exit 2; }
HAVE_CVC5=1
[ -x "$CVC5" ] || { echo "NOTE: cvc5 absent at $CVC5; its columns will read 'absent'" >&2; HAVE_CVC5=0; }

OUTDIR="$(dirname -- "$OUT")/refcaptures-$SHARD"
mkdir -p "$OUTDIR" || exit 2

printf 'file\tz3s6\tz3s6_ms\tz3s2\tz3s2_ms\tcvc5\tcvc5_ms\n' > "$OUT"

verdict_of() { grep -m1 -oE '^(sat|unsat|unknown|timeout)$' -- "$1" 2>/dev/null || true; }

run_z3() {  # $1 = solver id, $2 = file, $3 = capture; echoes elapsed ms
  local t0 t1
  t0=$(date +%s%N)
  timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
    bash -c "ulimit -v $VLIM; exec \"\$0\" -st -T:$BUDGET smt.arith.solver=\"\$1\" \"\$2\"" \
    "$Z3" "$1" "$2" > "$3" 2>&1
  t1=$(date +%s%N)
  printf '%s' "$(( (t1 - t0) / 1000000 ))"
}

while read -r rel; do
  [ -z "$rel" ] && continue
  f="$CORPUS$rel"
  if [ ! -r "$f" ]; then echo "UNREADABLE $rel" >&2; continue; fi
  slug="$(printf '%s' "$rel" | tr '/' '_')"

  ms6=$(run_z3 6 "$f" "$OUTDIR/$slug.z3s6.txt")
  v6=$(verdict_of "$OUTDIR/$slug.z3s6.txt")
  ms2=$(run_z3 2 "$f" "$OUTDIR/$slug.z3s2.txt")
  v2=$(verdict_of "$OUTDIR/$slug.z3s2.txt")

  vc="absent"; msc=0
  if [ "$HAVE_CVC5" = "1" ]; then
    t0=$(date +%s%N)
    timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
      bash -c "ulimit -v $VLIM; exec \"\$0\" --stats --tlimit=$((BUDGET * 1000)) \"\$1\"" \
      "$CVC5" "$f" > "$OUTDIR/$slug.cvc5.txt" 2>&1
    t1=$(date +%s%N)
    msc=$(( (t1 - t0) / 1000000 ))
    vc=$(verdict_of "$OUTDIR/$slug.cvc5.txt")
  fi

  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$rel" "${v6:-none}" "$ms6" "${v2:-none}" "$ms2" "${vc:-none}" "$msc" >> "$OUT"
done < "$LIST"

echo "REF-SHARD-DONE $SHARD $(($(wc -l < "$OUT") - 1)) rows"
