#!/usr/bin/env bash
# LRA-ATOM-SCREEN ladder driver.
#
# # The measurement design, and why it is not a brute-force sweep
#
# `AXEYUM_LRA_ATOM_SCREEN` (crates/axeyum-solver/src/lra_theory.rs) gates
# exactly ONE boolean: `atom_terms.len() > admitted_atoms`, where
# `admitted_atoms = (budget_bytes / BYTES_PER_ADMITTED_ATOM) * multiplier`.
# Nothing downstream of that comparison reads the multiplier or
# `admitted_atoms` itself -- `CdcltLraTheory::new` is built from the actual
# atom list and `budget_bytes`, not from the screen's allowance. So for a
# FIXED file, execution is a step function of the multiplier: refused for
# every multiplier below `ceil(atoms / (budget_bytes/BYTES_PER_ADMITTED_ATOM))`,
# and -- for every multiplier at or above it -- BIT-IDENTICAL to whatever the
# smallest admitting multiplier produces, because the only thing that changed
# is a threshold check that already passed.
#
# That means: (a) a file whose atom count is at or below the shipped
# allowance (1,024 at the default budget) behaves identically at every
# multiplier and needs exactly ONE run, ever; (b) a file above that
# allowance needs exactly TWO runs, ever -- refused (already have it: this
# IS the shipped arm) and admitted (one run at any multiplier at or above its
# own threshold) -- and that single "admitted" measurement is the real,
# measured answer for EVERY ladder level at or above that file's threshold,
# not an extrapolation across untested code. Running the same file five more
# times at 2x/4x/16x/1024x would re-execute the identical binary on the
# identical input through the identical code path and report the same
# number with more noise.
#
# So this driver runs THREE passes, not five:
#   1. `shipped`   -- multiplier 1, every file in the population (the loss
#                      control AND the source of each refused file's exact
#                      atom count, read from the admission-screen detail
#                      string).
#   2. `open`      -- a multiplier (see OPEN_MULT below) safely above the
#                      largest atom count in this corpus, run ONLY on files
#                      the `shipped` pass refused via the admission screen.
#                      Interleaved per file against a fresh `shipped` re-run
#                      (not the pass-1 result) so ambient flip is visible on
#                      the SAME pairing the brief asks for.
#   3. `spotcheck` -- a handful of files the `shipped` pass did NOT refuse,
#                      re-run at OPEN_MULT as an empirical control on the
#                      step-function claim above (source-reading is not
#                      evidence; this is).
#
# Each ladder level's (2x, 4x, 16x, "off") table is then DERIVED, per file,
# from whichever of these three passes actually executed that file at a
# multiplier on the correct side of its threshold -- see `derive_ladder.py`.
# This is documented as a derivation, not hidden as a raw run.
#
# Usage: run-ladder.sh <list> <outdir> <core> <bin> [budget_s]
set -u
LIST="$1"; OUTDIR="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/
HERE="$(cd -- "$(dirname -- "$0")" && pwd)"
# Two layouts: in-repo (bench-results/lra-atom-screen-20260916/, two levels
# under the repo root's scripts/) and the NAS harness copy deployed for the
# actual runs (self-contained, scripts/ one level under HERE). Prefer
# whichever actually exists rather than assuming the caller's layout.
if [ -x "$HERE/scripts/ledger-run-one.sh" ]; then
  LEDGER_RUN="$HERE/scripts/ledger-run-one.sh"
else
  REPO_ROOT="$(cd -- "$HERE/../.." && pwd)"
  LEDGER_RUN="$REPO_ROOT/scripts/ledger-run-one.sh"
fi
WRAP="$HERE/rss-wrap.sh"
LEDGER_DIR="$OUTDIR/ledger"
RSSDIR="$OUTDIR/rss"

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -r "$LIST" ] || { echo "ABORT: $LIST unreadable"; exit 2; }
[ -x "$LEDGER_RUN" ] || { echo "ABORT: $LEDGER_RUN missing"; exit 2; }
mkdir -p "$OUTDIR" "$LEDGER_DIR" "$RSSDIR" || exit 2

AX_SHA=$(sha256sum "$AX" | cut -d' ' -f1)

run_one() {  # $1 = arm name (also the AXEYUM_LRA_ATOM_SCREEN value), $2 = rel path
  local arm="$1" rel="$2" f slug rssout
  f="$CORPUS$rel"
  slug="$(printf '%s' "$rel" | tr '/' '_')"
  rssout="$RSSDIR/${arm}__${slug}.rss"
  [ -s "$rssout" ] && { echo "SKIP (already have) $arm $rel"; return 0; }
  REAL_BIN="$AX" RSS_OUT="$rssout" AXEYUM_LRA_ATOM_SCREEN="$arm" \
    "$LEDGER_RUN" \
      --sweep-id lra-atom-screen-20260916 \
      --arm "$arm" \
      --binary "$WRAP" \
      --binary-sha "$AX_SHA" \
      --file "$f" \
      --corpus-root "$CORPUS" \
      --outdir "$OUTDIR/captures" \
      --budget-s "$BUDGET" \
      --headroom-s "$HEADROOM" \
      --vlimit-kb "$VLIM" \
      --core "$PIN" \
      --ledger-dir "$LEDGER_DIR" \
      --note "lra-atom-screen ladder, AXEYUM_LRA_ATOM_SCREEN=$arm" \
    2>&1 | grep -E '^(LEDGER-ROW|ledger-run-one:)'
}

case "${PHASE:-shipped}" in
  shipped)
    n=0
    while read -r rel; do
      [ -z "$rel" ] && continue
      n=$((n + 1))
      run_one shipped "$rel"
    done < "$LIST"
    echo "PHASE shipped DONE $n files"
    ;;
  open)
    # LIST here is the candidates-to-admit file; interleave shipped vs open
    # per file, alternating which goes first.
    n=0
    while read -r rel; do
      [ -z "$rel" ] && continue
      n=$((n + 1))
      if [ $((n % 2)) -eq 1 ]; then
        run_one shipped "$rel"; run_one "${OPEN_MULT:?}" "$rel"
      else
        run_one "${OPEN_MULT:?}" "$rel"; run_one shipped "$rel"
      fi
    done < "$LIST"
    echo "PHASE open DONE $n files (multiplier ${OPEN_MULT:?})"
    ;;
  *) echo "ABORT: unknown PHASE '${PHASE:-}'"; exit 2 ;;
esac
