#!/usr/bin/env bash
# A13-QUANT (ADR-2149): run one binary on ADR-2113's 53 reference-minimal
# UFLIA cores under ONE environment arm, with the per-universal admission
# census on, so `split.py` can split `rej_nocontext` (= `inactive_dropped`)
# into crossed-binder / negative / untracked per core and read the lazy
# discovery driver's counters at every loop exit.
#
#   census-run.sh <cores.list> <outdir> <pin> <bin> <arm> [budget_s]
#
# <arm> is `off` (every lever variable UNSET -- the shipped arm, byte for
# byte; an explicit `=0` takes a different path through `cap_lever!`) or
# `on` (AXEYUM_QINST_POSITIVE_PATH=1, ADR-2120's level 1) or `composed`
# (level 1 + AXEYUM_QINST_GROUND_SESSION=2, ADR-2130's session lever, the
# composition QUANT-COMPOSE sized), or
# `nested1`/`nested2` (AXEYUM_QINST_NESTED_ACTIVATION at that level, alone),
# `nested2-on` (level 2 + ADR-2120's level 1) or `nested2-composed` (all three).
#
# Budget 24 s / 8 GiB, the envelope ADR-2120 s7 / ADR-2133 / QUANT-REACH-DIFF
# used on the same cores. Timing is `$EPOCHREALTIME`, never `date +%N`: on
# s5/s7 (uutils) `%3N` prints nanoseconds and every `_ms` column is off by
# 10^6 (CLAUDE.md memory, QUANT-COMPOSE s6).
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; ARM="$5"; BUDGET="${6:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
case "$ARM" in
  off) ARMENV=() ;;
  on) ARMENV=(AXEYUM_QINST_POSITIVE_PATH=1) ;;
  composed) ARMENV=(AXEYUM_QINST_POSITIVE_PATH=1 AXEYUM_QINST_GROUND_SESSION=2) ;;
  nested1) ARMENV=(AXEYUM_QINST_NESTED_ACTIVATION=1) ;;
  nested2) ARMENV=(AXEYUM_QINST_NESTED_ACTIVATION=2) ;;
  nested2-on) ARMENV=(AXEYUM_QINST_NESTED_ACTIVATION=2 AXEYUM_QINST_POSITIVE_PATH=1) ;;
  nested2-composed) ARMENV=(AXEYUM_QINST_NESTED_ACTIVATION=2 AXEYUM_QINST_POSITIVE_PATH=1 AXEYUM_QINST_GROUND_SESSION=2) ;;
  *) echo "ABORT: unknown arm $ARM"; exit 2 ;;
esac
mkdir -p "$OUT/raw"
SUMMARY="$OUT/run-summary.tsv"
printf 'core\tarm\trc\tverdict\tdecided_by\telapsed_ms\n' > "$SUMMARY"
{
  echo "host=$(hostname) pin=$PIN arm=$ARM budget_s=$BUDGET vlim_kb=$VLIM"
  echo "bin=$AX sha256=$(sha256sum "$AX" | cut -d' ' -f1)"
  echo "started=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
} > "$OUT/RUN-HEADER.txt"

n=0
total=$(wc -l < "$LIST")
while IFS= read -r f; do
  [ -n "$f" ] || continue
  n=$((n + 1))
  b="$(basename "$f")"
  t0=$EPOCHREALTIME
  env -u AXEYUM_QINST_POSITIVE_PATH -u AXEYUM_QINST_GROUND_SESSION \
      -u AXEYUM_QINST_NESTED_ACTIVATION -u AXEYUM_QINST_GEN_LADDER -u AXEYUM_MACRO_INLINE \
      "${ARMENV[@]}" \
      AXEYUM_QTRACE=1 AXEYUM_QPROBE=1 AXEYUM_QPROBE_CENSUS=1 \
    timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
    bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
    "$AX" "$f" > "$OUT/raw/$b.out" 2> "$OUT/raw/$b.err"
  rc=$?
  t1=$EPOCHREALTIME
  ms=$(awk -v a="$t0" -v b="$t1" 'BEGIN { printf "%d", (b - a) * 1000 }')
  v=$(grep -m1 -oE '^(sat|unsat|unknown)$' "$OUT/raw/$b.out" 2>/dev/null || true)
  decided=$(grep -m1 -oE 'decided_by=[^ ]+' "$OUT/raw/$b.out" 2>/dev/null | head -1 || true)
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$b" "$ARM" "$rc" "${v:-NOVERDICT}" "${decided:-NA}" "$ms" >> "$SUMMARY"
  printf 'RUN %3d/%s %s arm=%s rc=%s v=%s ms=%s\n' "$n" "$total" "$b" "$ARM" "$rc" "${v:-NOVERDICT}" "$ms"
done < "$LIST"
echo "finished=$(date -u +%Y-%m-%dT%H:%M:%SZ) cores=$n" >> "$OUT/RUN-HEADER.txt"
echo "CENSUS-DONE arm=$ARM $n cores -> $OUT"
touch "$OUT/DONE"
