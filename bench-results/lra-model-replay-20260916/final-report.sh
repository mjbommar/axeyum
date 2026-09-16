#!/usr/bin/env bash
# Final analysis, run on s7 where the captures live. Emits everything the
# write-up needs and nothing that has to be retyped by hand.
set -u
cd ~/lra-model-replay-work || exit 2
OUT=/tmp/lra-model-replay-final
rm -rf "$OUT"; mkdir -p "$OUT"

echo "############ BASELINE (shipped binary, screen UNSET) ############"
echo "rows: $(($(wc -l < out-baseline/ledger-baseline.tsv) - 1))"
echo "binary sha256: $(sha256sum smtcomp_cli.baseline | cut -d' ' -f1)"
echo "--- verdicts ---"
awk -F'\t' 'NR>1{print $3}' out-baseline/ledger-baseline.tsv | sort | uniq -c | sort -rn
echo "--- DECIDED (sat+unsat) ---"
awk -F'\t' 'NR>1 && ($3=="sat"||$3=="unsat"){n++} END{print n+0}' out-baseline/ledger-baseline.tsv
echo "--- exit statuses ---"
awk -F'\t' 'NR>1{print $4}' out-baseline/ledger-baseline.tsv | sort | uniq -c | sort -rn

echo
echo "############ CENSUS ARM (screen=16, census on) ############"
echo "rows: $(($(wc -l < out-census/ledger-census.tsv) - 1))"
echo "binary sha256: $(sha256sum smtcomp_cli.census | cut -d' ' -f1)"
echo "--- verdicts ---"
awk -F'\t' 'NR>1{print $3}' out-census/ledger-census.tsv | sort | uniq -c | sort -rn
echo "--- DECIDED (sat+unsat) ---"
awk -F'\t' 'NR>1 && ($3=="sat"||$3=="unsat"){n++} END{print n+0}' out-census/ledger-census.tsv

echo
echo "############ ANALYSIS ############"
python3 analyze-census.py out-census/cap census out-census/ledger-census.tsv "$OUT"

echo
echo "############ TARGET POPULATION, PER FILE ############"
python3 - "$OUT/per-file.tsv" <<'PY'
import sys, csv
rows = list(csv.DictReader(open(sys.argv[1]), delimiter='\t'))
tgt = [r for r in rows if r['last_arm'] in ('no-model','no-replay')]
print(f"target files: {len(tgt)}")
hdr = ('file','last_arm','atoms','order','equality','unsupported',
       'eq_asserted_false','assertions','assert_false','assert_eval_err',
       'simplex_rows','model_decline','construct','ms','exit')
print('\t'.join(hdr))
for r in sorted(tgt, key=lambda r: (r['last_arm'], r['file'])):
    print('\t'.join(str(r.get(k,'')) for k in hdr))
PY

echo
echo "############ CROSS-CHECK: simplex_rows=n/a vs fm-fallback ############"
python3 - "$OUT/per-file.tsv" <<'PY'
import sys, csv, collections
rows = list(csv.DictReader(open(sys.argv[1]), delimiter='\t'))
tgt = [r for r in rows if r['last_arm'] in ('no-model','no-replay')]
c = collections.Counter(
    (r['model_decline'].split('|')[0] if r['model_decline'] else '(model built)',
     'tableau ABSENT' if r['simplex_rows'] in ('n/a','') else 'tableau present')
    for r in tgt)
for k,v in sorted(c.items(), key=lambda kv:-kv[1]):
    print(f"{v:4d}  {k[0]:<28s} {k[1]}")
print()
print("unsupported-atom count over the whole target population:",
      sum(int(r['unsupported'] or 0) for r in tgt))
print("files with any unsupported atom:",
      sum(1 for r in tgt if int(r['unsupported'] or 0) > 0))
PY

cp "$OUT/per-file.tsv" "$OUT/histogram.tsv" . 2>/dev/null
echo
echo "artifacts in $OUT and copied to ~/lra-model-replay-work/"
