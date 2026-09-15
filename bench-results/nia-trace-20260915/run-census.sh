#!/usr/bin/env bash
# Runs `nia_estimate_census` over a paths file, one process per file so a single
# pathological target cannot take the sweep down with it (lane NIA-TRACE,
# ADR-2112).
#
# `ulimit -v` is per child: forcing lowering on a refused file can allocate tens
# of GB, and a ceiling turns that into an allocation failure (a result) instead
# of an OOM kill (not a result). Files that trip it are reported as
# `LIMIT-EXCEEDED` rows rather than silently dropped -- a tool that omits rather
# than refuses turns the output into a measurement of the accepted subset.
#
# usage: run-census.sh <paths-file> <out.tsv> [--actual] [--widths 4,8,32]
set -uo pipefail

PATHS=${1:?paths file}
OUT=${2:?output tsv}
shift 2

BIN=${BIN:-target/release/examples/nia_estimate_census}
VLIMIT=${VLIMIT:-16000000}
PERFILE=${PERFILE:-600}

[ -x "$BIN" ] || { echo "no census binary at $BIN" >&2; exit 2; }

# Header from a run with no targets is not available (the tool needs one), so
# take it from the first successful file and keep it.
: > "$OUT"
header_written=0
n=0
skipped=0

while IFS= read -r file; do
    [ -n "$file" ] || continue
    n=$((n + 1))
    out=$( (ulimit -v "$VLIMIT"; timeout -k 5 "$PERFILE" "$BIN" "$@" "$file") 2>&1 )
    rc=$?
    if [ "$rc" -ne 0 ]; then
        skipped=$((skipped + 1))
        printf '%s\tLIMIT-EXCEEDED\trc=%s\n' "$file" "$rc" >> "$OUT"
        printf 'SKIP rc=%s %s\n' "$rc" "$file" >&2
        continue
    fi
    if [ "$header_written" -eq 0 ]; then
        head -1 <<<"$out" >> "$OUT"
        header_written=1
    fi
    tail -n +2 <<<"$out" >> "$OUT"
    printf '%d done\n' "$n" >&2
done < "$PATHS"

printf 'COMPLETE: %d files, %d over the limit or timed out\n' "$n" "$skipped" >&2
