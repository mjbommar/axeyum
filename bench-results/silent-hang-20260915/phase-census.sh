#!/usr/bin/env bash
# SILENT-HANG -- the census the bucket was never given.
#
# `skeleton-reach`'s fd-census.sh greps `^; route ` and `^; give-up `.  Those
# are the only two lines it reads, so a run whose worker never reached a route
# boundary is recorded as `bound_by=NONE` and the census has nothing more to
# say.  `smtcomp_cli --trace` ALSO prints, on exactly that watchdog path,
#
#     ; partial phase stack=<outermost>(ms)>…>…  in=<innermost> in_ms=<n> depth=<d> enters=<label>:<n>,…
#
# read from the LIVE worker by the watchdog thread while the worker is still
# inside the frame (`axeyum_solver::phase_breadcrumb`).  Nothing in the earlier
# census ever looked at that line.  This script reads it.
#
#   phase-census.sh <list> <out.tsv> <pin> [budget_s]
#
# Columns, and why each one is here:
#   verdict      re-derived in THIS run (R1); never inherited
#   rc           the process exit status, as its own channel (R7) -- a killed
#                process is not a process that answered `unknown`
#   bound_by     what the old census read, carried so the re-derivation is
#                comparable row for row
#   phase_in     the INNERMOST open frame: the code that was running when the
#                watchdog read the breadcrumb
#   phase_in_ms  how long it had been in that frame
#   depth        open frame count; `0` with a breadcrumb installed means the
#                worker was outside every instrumented phase -- a finding about
#                the INSTRUMENT, not about the solver, and it must be rendered
#                differently from "no breadcrumb at all" (no phase line)
#   phase_line   the whole line, verbatim, so the bucketing can be redone
#                without re-running anything (R4: never size a bucket by a label)
#   peak_rss_kb  VmHWM of the process -- a wall-clock timeout bounds neither
#                memory nor progress (R15)
set -u
LIST="$1"
OUT="$2"
PIN="${3:-1}"
BUDGET="${4:-24}"
CORPUS="${SH_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
AX="${SH_AX:-/nas3/data/axeyum/harness/silent-hang/bin/smtcomp_cli-sh}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

printf 'file\tverdict\trc\tms\tbound_by\troute_line\tphase_in\tphase_in_ms\tdepth\tpeak_rss_kb\tgiveup_kind\tphase_line\n' > "$OUT"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  [ -r "$CORPUS/$f" ] || { printf '%s\tNO-FILE\t-\t-\t-\t-\t-\t-\t-\t-\t-\n' "$f" >> "$OUT"; continue; }
  t0=$(( $(date +%s%N) / 1000000 ))
  raw=$(AXEYUM_TRACE=1 timeout $((BUDGET + 120)) taskset -c "$PIN" \
          /usr/bin/time -f 'SHPEAKRSS %M' "$AX" "$CORPUS/$f" --timeout-ms $((BUDGET * 1000)) 2>&1)
  rc=$?
  t1=$(( $(date +%s%N) / 1000000 ))
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
  bb=$(printf '%s\n' "$raw" | grep -m1 '^; route ' | grep -oE 'bound_by=[^ ]+' | cut -d= -f2 || true)
  gk=$(printf '%s\n' "$raw" | grep -m1 '^; give-up ' | grep -oE 'kind=[A-Za-z]+' | cut -d= -f2 || true)
  pl=$(printf '%s\n' "$raw" | grep -m1 '^; partial phase ' | tr '\t\n' '  ' || true)
  pin_=$(printf '%s' "$pl" | grep -oE ' in=[^ ]+' | head -1 | cut -d= -f2)
  pms=$(printf '%s' "$pl" | grep -oE ' in_ms=[^ ]+' | head -1 | cut -d= -f2)
  dep=$(printf '%s' "$pl" | grep -oE ' depth=[0-9]+' | head -1 | cut -d= -f2)
  rss=$(printf '%s\n' "$raw" | grep -oE '^SHPEAKRSS [0-9]+' | tail -1 | awk '{print $2}')
  # R4: `bound_by=NONE` in the earlier census covers THREE program points and
  # the old parser could not tell them apart.  Split before counting.
  #   attributed   a `; route ... bound_by=X` line -- a route finished
  #   unavailable  a `; route unavailable: <reason>` line -- the run reached the
  #                watchdog and the ROUTE board held nothing, i.e. not even
  #                `fd:parse` had returned
  #   absent       neither line exists -- the PROCESS died before `main` printed
  #                (external kill / OOM / abort), which is not a solver verdict
  if printf '%s\n' "$raw" | grep -q '^; route .*bound_by='; then rk=attributed
  elif printf '%s\n' "$raw" | grep -q '^; route unavailable:'; then rk=unavailable
  elif printf '%s\n' "$raw" | grep -q '^; partial route '; then rk=partial
  else rk=absent; fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$f" "${v:-NONE}" "$rc" "$((t1-t0))" "${bb:-NONE}" "$rk" \
    "${pin_:-NO-PHASE-LINE}" "${pms:-na}" "${dep:-na}" "${rss:-na}" "${gk:-NONE}" \
    "${pl:-NO-PHASE-LINE}" >> "$OUT"
  printf '%-56s %-8s rc=%-3s %6sms bb=%-14s route=%-12s in=%-24s in_ms=%-7s d=%-3s rss=%s\n' \
    "$(basename "$f")" "${v:-NONE}" "$rc" "$((t1-t0))" "${bb:-NONE}" "$rk" \
    "${pin_:-NO-PHASE-LINE}" "${pms:-na}" "${dep:-na}" "${rss:-na}"
done < "$LIST"
echo "DONE $OUT"
