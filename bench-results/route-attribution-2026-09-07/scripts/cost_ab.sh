#!/usr/bin/env bash
# A/B for the "no measurable cost in the shipping path" claim (ADR-1760).
#
# The claim is that with route attribution OFF -- which is the default, and how
# every recorded parity baseline runs -- the added cost is one thread-local
# `Cell<bool>` read per recording site. That is an argument about the code. This
# measures it, because a comment asserting a cost is not a measurement of one.
#
# Protocol: the SAME file list, alternating arms (baseline, instrumented,
# baseline, ...) so any drift in machine load is shared between them rather than
# accumulating on whichever arm ran second. NO `--trace` on either arm -- the
# question is the default path, not the collecting one.
#
# Arms are two prebuilt release binaries, per the standing rule that
# `cargo-serialized.sh` takes a host-wide flock and so a timing run through it
# measures the queue rather than the code.
set -uo pipefail

BASE_BIN="$1"    # smtcomp_cli built at the pre-attribution commit
NEW_BIN="$2"     # smtcomp_cli built at HEAD
LIST="$3"
OUT_TSV="$4"
N="${5:-60}"
BUDGET_S="${6:-10}"
REPS="${7:-3}"

printf 'rep\tarm\tfile\twall_ms\tverdict\n' > "$OUT_TSV"

for rep in $(seq 1 "$REPS"); do
  for arm in base new; do
    case "$arm" in
      base) BIN="$BASE_BIN" ;;
      new)  BIN="$NEW_BIN" ;;
    esac
    idx=0
    head -n "$N" "$LIST" | while IFS= read -r file; do
      idx=$((idx + 1))
      [ -z "$file" ] && continue
      start_ns=$(date +%s%N)
      out=$(timeout -k 5 $(( BUDGET_S * 2 + 10 )) "$BIN" "$file" \
              --timeout-ms "$((BUDGET_S * 1000))" 2>/dev/null | tail -1)
      end_ns=$(date +%s%N)
      printf '%s\t%s\t%s\t%s\t%s\n' "$rep" "$arm" "$file" \
        "$(( (end_ns - start_ns) / 1000000 ))" "${out:-none}" >> "$OUT_TSV"
    done
  done
done
