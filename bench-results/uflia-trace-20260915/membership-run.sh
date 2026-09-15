#!/usr/bin/env bash
# UFLIA-TRACE -- dump our ground set per core and ask whether z3's substituted
# terms are in it.
#
#   membership-run.sh <list-of-core-basenames> <outdir> <bin> <inst-dir> [budget_s]
#
# UNPINNED ON PURPOSE when this lane's pinned cores are busy, and that is sound
# in ONE direction only: load can only make the run accumulate FEWER ground
# terms, so a term reported PRESENT was definitely built, while a term reported
# ABSENT may be one a quieter run would have built. `ground-membership.py` states
# the same asymmetry. Do not read an ABSENT column from a loaded run as "we
# cannot construct these".
set -u
LIST="$1"; OUTDIR="$2"; AX="$3"; INSTDIR="$4"; BUDGET="${5:-24}"
CORES=/nas3/data/axeyum/harness/core-select/cores
HERE="$(cd "$(dirname "$0")" && pwd)"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
mkdir -p "$OUTDIR"

while IFS= read -r b; do
  [ -n "$b" ] || continue
  [ -r "$CORES/$b" ] || { echo "SKIP $b (no core file)"; continue; }
  [ -r "$INSTDIR/$b.inst" ] || { echo "SKIP $b (no instance file)"; continue; }
  # Dumps are KEPT: they are the expensive half (a solve each) and the cheap
  # half (the comparison) is the one that gets corrected. Write them somewhere
  # that is not /tmp -- /tmp here is a tmpfs in RAM and a 16 MB dump per core
  # is a real contribution to an OOM.
  d="$OUTDIR/$b.dump"
  rm -f "$d"
  AXEYUM_QGROUNDDUMP="$d" timeout $((BUDGET + 40)) \
    "$AX" "$CORES/$b" --timeout-ms $((BUDGET * 1000)) >/dev/null 2>&1
  echo "==== $b"
  if [ -s "$d" ]; then
    python3 "$HERE/ground-membership.py" "$d" "$INSTDIR/$b.inst"
  else
    echo "NO-GROUND-DUMP  nothing was written; not a measurement of absence"
  fi
done < "$LIST"
echo "MEMBERSHIP-DONE"
