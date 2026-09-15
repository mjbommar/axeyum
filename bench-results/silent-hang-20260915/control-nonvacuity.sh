#!/usr/bin/env bash
# SILENT-HANG -- is the CONTROL non-vacuous?
#
# "The control did not move" is worth nothing if the changed code never runs on
# it.  The control is the 53 DECIDED `UFNIA` rows; the changed code is
# `collect_eq_atoms`, whose biggest caller is the first statement of the
# `euf:offline` phase (`euf_egraph.rs:1468-1473`).
#
# The obstacle: a DECIDED row returns normally, and the `; partial phase`
# breadcrumb prints only on the WATCHDOG path -- so on exactly the rows that
# make a good control, the instrument that would show the route is silent.
#
# The probe: run each row at a budget BELOW ITS OWN measured solve time, so the
# watchdog fires mid-route and the breadcrumb prints.  No verdict from this run
# is used for anything; it exists solely to make the phase reading available.
#
# THE FIRST VERSION OF THIS PROBE USED A FLAT 1200 ms AND REPORTED
# "0 of 53 entered an `euf:` frame".  That was the PROBE failing, not the
# control being vacuous: `phase_line_present` was `no` on all 53, because these
# rows are fast (that is why they are decided) and finished before the watchdog.
# A zero from an instrument never shown to fire is indistinguishable from a
# strong negative, so the budget is now derived PER ROW from the committed
# census, and `phase_line_present` is checked BEFORE the `euf:` count is read.
set -u
W="$(cd "$(dirname "$0")" && pwd)"
LIST="${1:-$W/lists/control-decided-ufnia.list}"
OUT="${2:-$W/ref/control-nonvacuity.tsv}"
PIN="${3:-5}"
CENSUS="$W/../skeleton-reach-20260914/ref/fd-census-208.tsv"
CORPUS="${SH_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
AX="${SH_AX_AB:-/nas3/data/axeyum/harness/silent-hang/bin/smtcomp_cli-ab}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -r "$CENSUS" ] || { echo "ABORT: census $CENSUS missing"; exit 2; }

printf 'file\tprobe_ms\tphase_line_present\teuf_frame\tenters_euf\n' > "$OUT"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  # 40 % of the row's own measured solve time, floored at 60 ms: low enough to
  # land inside the route, high enough to get past ingest.
  own=$(awk -F'\t' -v f="$f" '$1==f{print $6; exit}' "$CENSUS")
  [ -n "${own:-}" ] && [ "$own" -gt 0 ] 2>/dev/null || own=1000
  pms=$((own * 2 / 5)); [ "$pms" -lt 60 ] && pms=60
  raw=$(AXEYUM_TRACE=1 timeout 120 taskset -c "$PIN" "$AX" "$CORPUS/$f" \
          --timeout-ms "$pms" 2>&1)
  pl=$(printf '%s\n' "$raw" | grep -m1 '^; partial phase ' || true)
  if [ -z "$pl" ]; then
    printf '%s\t%s\tno\t-\t-\n' "$f" "$pms" >> "$OUT"; continue
  fi
  ent=$(printf '%s' "$pl" | grep -oE 'enters=[^ ]*' | cut -d= -f2-)
  dpst=$(printf '%s' "$pl" | grep -oE 'deepest=[^ ]*' | cut -d= -f2-)
  euf=$(printf '%s\n%s\n' "$ent" "$dpst" | tr ',>' '\n\n' | grep -c '^euf:' || true)
  if [ "${euf:-0}" -gt 0 ]; then k=yes; else k=no; fi
  printf '%s\t%s\tyes\t%s\t%s\n' "$f" "$pms" "$k" \
    "$(printf '%s\n%s\n' "$ent" "$dpst" | tr ',>' '\n\n' | grep -oE '^euf:[^ ]*' | sort -u | tr '\n' ' ')" >> "$OUT"
done < "$LIST"

echo "=== control non-vacuity ==="
awk -F'\t' 'NR>1{n++; if ($3=="yes") pl++; if ($4=="yes") e++} END {
  printf "control rows probed                : %d\n", n;
  printf "breadcrumb PRINTED (the probe fired): %d   <- read this BEFORE the next line\n", pl+0;
  printf "an `euf:` frame was ENTERED         : %d   <- the changed call site executes here\n", e+0;
  if (pl+0 == 0) { print "FINDING-CHECK FAILED: the PROBE never fired -- this says nothing about the control"; exit 2 }
  if (e+0 == 0)  { print "FINDING-CHECK FAILED: the control is VACUOUS -- the changed code never ran on it"; exit 1 }
}' "$OUT"
echo "DONE $OUT"
