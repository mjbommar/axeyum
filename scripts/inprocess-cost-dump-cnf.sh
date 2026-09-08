#!/usr/bin/env bash
# Bit-blast each `.smt2` in a list to DIMACS, so the per-pass tools can run over
# the SAME encoding the SMT front door hands the SAT core.
#
# Usage:
#   scripts/inprocess-cost-dump-cnf.sh <files.txt> <out_dir>
#
# WHY THE ENCODING HAS TO BE CHECKED, NOT ASSUMED
#
# `dump_dimacs` mirrors the word-level preprocessing the fair runs use and then
# bit-blasts. "Mirrors" is a claim about two code paths that can drift, and a
# per-pass measurement taken over a DIFFERENT formula than the solver actually
# solves is worthless in a way that produces perfectly plausible numbers. So the
# solver's own `cnf_variables`/`cnf_clauses` counters (printed by
# `inprocess_ab`) must equal the `p cnf` header this writes. Check one file both
# ways before trusting a batch of them; this script prints the header it wrote
# so the comparison needs no second tool.
#
# Files are dumped on the E-cores by default so a concurrent timing sweep pinned
# to the P-cores is not competing with this for a core.
set -uo pipefail

cd "$(dirname "$0")/.."

files="${1:-}"
out_dir="${2:-}"
if [[ -z "$files" || -z "$out_dir" ]]; then
  echo "usage: scripts/inprocess-cost-dump-cnf.sh <files.txt> <out_dir>" >&2
  exit 2
fi
mkdir -p "$out_dir"

bin="target/release/examples/dump_dimacs"
if [[ ! -x "$bin" ]]; then
  echo "FAIL: missing $bin" >&2
  exit 2
fi

cpus="${DUMP_CPUS:-12-15}"
mem_gb="${MEM_GB:-24}"
per_file_s="${DUMP_TIMEOUT_S:-600}"

index=0
ok=0
failed=0
while IFS= read -r file; do
  [[ -z "${file// }" ]] && continue
  index=$(( index + 1 ))
  name=$(printf '%02d_%s' "$index" "$(basename "$file" .smt2)")
  target="$out_dir/$name.cnf"
  if MEM_LIMIT_GB="$mem_gb" timeout "$per_file_s" \
     taskset -c "$cpus" ./scripts/mem-run.sh "$bin" "$file" "$target" >/dev/null 2>&1; then
    ok=$(( ok + 1 ))
    echo "$name  $(head -1 "$target")  <- $file"
  else
    failed=$(( failed + 1 ))
    # A file that cannot be bit-blast inside the cap is a REPORTED absence, not
    # a silently shorter corpus: a per-pass table over "the files that happened
    # to dump" is a table about a population nobody chose.
    rm -f "$target"
    echo "FAILED-TO-DUMP  $file"
  fi
done <"$files"

echo "dumped=$ok failed=$failed attempted=$index"
