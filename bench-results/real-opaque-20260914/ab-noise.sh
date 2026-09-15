#!/usr/bin/env bash
# REAL-OPAQUE R6 -- the NOISE FLOOR: the SAME arm, twice, over a whole division.
#
# Assume the band is not zero until measured. Ambient load has moved 23 verdicts
# in one division at fixed code on these boxes (ADR-2000), so a "+14" that is not
# compared against a same-arm A/A is a number with no error bar.
#
# Identical to `ab-run.sh` in every respect -- same pinning, same interleaving,
# same rotation, same wrapper timeout, same `ulimit -v`, same exit-status
# channel -- EXCEPT that both halves run the SHIPPED arm. Any row that moves here
# moved for a reason that is not the lever.
#
# Usage: ab-noise.sh <list> <out.tsv> <core> <bin> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=${REAL_OPAQUE_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }
[ -s "$LIST" ] || { echo "ABORT: $LIST is empty or missing"; exit 2; }

resolve() { case "$1" in /*) printf '%s' "$1" ;; *) printf '%s/%s' "$CORPUS" "$1" ;; esac; }
FIRST=$(resolve "$(head -1 "$LIST")")
[ -r "$FIRST" ] || { echo "ABORT: first list entry is unreadable: $FIRST"; exit 2; }

run_arm() {
  local f="$1" t0 t1 raw rc v ex dby bby refused
  t0=$(date +%s%N)
  raw=$(env -u AXEYUM_LRA_OPAQUE_APPS AXEYUM_TRACE=1 \
          timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$(resolve "$f")" 2>&1)
  rc=$?
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$'); v="${v:-NONE}"
  case "$rc" in
    0) ex=ok ;; 124) ex=timeout ;; 134) ex=rc134 ;; 137) ex=sigkill ;; *) ex="rc$rc" ;;
  esac
  dby=$(printf '%s' "$raw" | grep -oE 'decided_by=[^ ]*' | head -1 | cut -d= -f2)
  bby=$(printf '%s' "$raw" | grep -oE 'bound_by=[^ ]*' | head -1 | cut -d= -f2)
  if printf '%s' "$raw" | grep -qF 'unsupported arithmetic atom'; then refused=refused
  else refused=clean; fi
  printf '%s\t%s\t%s\t%s|%s|%s' "$v" "$(((t1 - t0) / 1000000))" "$ex" \
    "${dby:-NONE}" "${bby:-NONE}" "$refused"
}

# The column names are `off_*` / `on_*` so `ab-summarize.py` reads this file
# unchanged; BOTH are the shipped arm and the header says so.
printf '# NOISE FLOOR: both halves are the SHIPPED arm (env -u). Column names kept for the summariser.\n' > "$OUT"
printf 'file\torder\toff_verdict\toff_ms\toff_exit\toff_route\ton_verdict\ton_ms\ton_exit\ton_route\n' >> "$OUT"
n=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  n=$((n + 1))
  A=$(run_arm "$f"); B=$(run_arm "$f")
  printf '%s\tA-A\t%s\t%s\n' "$f" "$A" "$B" >> "$OUT"
done < "$LIST"
echo "DONE $OUT rows=$n core=$PIN budget=${BUDGET}s"
