#!/usr/bin/env bash
# QUANT-INSTANCE-PROBE step 1: extract z3's instantiations per core.
#
#   qip-extract.sh <cores.list> <outdir> <pin> <script_dir> [budget_s]
#
# For each core: runs z3 with :produce-proofs, saves the proof, extracts
# ground instance bodies with z3-proof-instances.py (under a 16 GB ulimit -v
# per CLAUDE.md "Measuring anything"), and reports raw/unique/unmatched
# counts for cross-check against ref-cores.tsv's proof_qinst column (the
# positive control this lane's brief asked for).
set -u
LIST="$1"; OUTDIR="$2"; PIN="$3"; SCRIPTDIR="$4"; BUDGET="${5:-60}"
mkdir -p "$OUTDIR/proof" "$OUTDIR/inst"
SUMMARY="$OUTDIR/extract-summary.tsv"
printf 'core\tz3_verdict\traw_count\tunique_bodies\tunmatched\n' > "$SUMMARY"

py() { bash -c "ulimit -v 16000000; exec python3 \"\$0\" \"\$@\"" "$@"; }

while IFS= read -r p; do
  [ -n "$p" ] || continue
  b="$(basename "$p")"
  tmp="$OUTDIR/proof/$b.query"
  { echo '(set-option :produce-proofs true)'; cat "$p"; echo '(get-proof)'; } > "$tmp"
  a=$(taskset -c "$PIN" timeout $((BUDGET + 20)) z3 -T:$BUDGET -smt2 "$tmp" 2>&1)
  v=$(printf '%s\n' "$a" | grep -m1 -oE '^(sat|unsat|unknown|timeout)$' || true)
  rm -f "$tmp"
  raw=0; uniq=0; unm="NOT-UNSAT-${v:-NOVERDICT}"
  if [ "${v:-}" = unsat ]; then
    printf '%s\n' "$a" > "$OUTDIR/proof/$b.proof"
    if py "$SCRIPTDIR/z3-proof-instances.py" "$OUTDIR/proof/$b.proof" --json \
        > "$OUTDIR/inst/$b.json" 2> "$OUTDIR/inst/$b.err"; then
      py "$SCRIPTDIR/z3-proof-instances.py" "$OUTDIR/proof/$b.proof" \
        > "$OUTDIR/inst/$b.asserts" 2>> "$OUTDIR/inst/$b.err"
      raw=$(python3 -c "import json; d=json.load(open('$OUTDIR/inst/$b.json')); print(d['raw_count'])")
      uniq=$(python3 -c "import json; d=json.load(open('$OUTDIR/inst/$b.json')); print(len(d['bodies']))")
      unm=$(python3 -c "import json; d=json.load(open('$OUTDIR/inst/$b.json')); print(d['unmatched'])")
    else
      raw=0; uniq=0; unm="EXTRACT-FAIL"
    fi
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "$b" "${v:-NOVERDICT}" "$raw" "$uniq" "$unm" >> "$SUMMARY"
done < "$LIST"
echo "DONE $SUMMARY"
