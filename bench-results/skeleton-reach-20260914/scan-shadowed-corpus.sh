#!/usr/bin/env bash
# SKELETON-REACH -- how wide is the operator-shadowing class, corpus-wide?
#
# The 655-row Tier 1 sample found 2 files (both `fp`). A sample of 655 cannot
# distinguish "2 files exist" from "2 landed in this sample". This walks the
# seven Tier 1 DIVISION DIRECTORIES in full.
#
#   scan-shadowed-corpus.sh <out.tsv>
#
# The alternation is BUILT FROM `apply_op`'s own source by scan-shadowed-ops.py
# (which asserts `fp` is in and `is` is out), never typed here: a literal list
# would measure the author's memory. A zero from a pattern never shown to match
# is indistinguishable from a strong negative, so the run prints a POSITIVE
# CONTROL hit count on the known file before reporting anything.
set -eu
OUT="$1"
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
CORPUS="${SKEL_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
KNOWN="UFNIA/vcc-havoc/verisoft-baby.c.10.privileged.smt2"

cd "$ROOT"
OPS="$(python3 - <<'PY'
import importlib.util, pathlib, sys
spec = importlib.util.spec_from_loader("s", loader=None)
src = pathlib.Path("bench-results/skeleton-reach-20260914/scan-shadowed-ops.py").read_text()
ns = {"__name__": "notmain"}
# Run only the definitions, not main().
exec(src.replace("\nmain()\n", "\n"), ns)
ops = ns["operator_names"]("crates/axeyum-smtlib/src/parse.rs")
import re
print("|".join(re.escape(o) for o in sorted(ops)))
PY
)"
[ -n "$OPS" ] || { echo "ABORT: empty operator alternation"; exit 2; }
PAT="\\((declare-fun|declare-const|define-fun|define-fun-rec)[[:space:]]+($OPS)[[:space:]]"

# POSITIVE CONTROL: the pattern must match the file we already read by hand.
if ! grep -qE "$PAT" "$CORPUS/$KNOWN"; then
  echo "ABORT: the pattern does not match the KNOWN shadowed file -- a zero would mean nothing"
  exit 3
fi
echo "CONTROL-OK: pattern matches $KNOWN"

printf 'division\tfile\tshadowed\n' > "$OUT"
for d in AUFDTLIRA AUFLIRA QF_NIA UF UFDTLIRA UFLIA UFNIA; do
  n=0
  while IFS= read -r p; do
    rel="${p#"$CORPUS"/}"
    names=$(grep -hoE "$PAT" "$p" | awk '{print $2}' | sort -u | paste -sd, -)
    printf '%s\t%s\t%s\n' "$d" "$rel" "$names" >> "$OUT"
    n=$((n + 1))
  done < <(grep -rlE "$PAT" "$CORPUS/$d" 2>/dev/null || true)
  echo "$d: $n shadowed of $(find "$CORPUS/$d" -name '*.smt2' | wc -l) files"
done
echo "DONE $OUT"
awk -F'\t' 'NR>1{c[$3]++} END{for (k in c) print c[k], k}' "$OUT" | sort -rn
