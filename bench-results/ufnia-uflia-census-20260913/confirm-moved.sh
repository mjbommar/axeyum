#!/usr/bin/env bash
# Re-check every row an A/B moved, three ways, with the EXIT STATUS depending on
# the finding.
#
# 1. REPRODUCIBILITY. ~1-1.5 % of files at a 24 s budget flip on ambient load, so
#    a single pairing is not a result. Each moved file is re-run THREE times per
#    arm at the board budget on one pinned core.
# 2. THE REFERENCES. Every newly decided file is re-run against z3 and cvc5 and
#    compared with the declared `:status`. Units differ and mixing them silently
#    corrupts a board: `z3 -T:<SECONDS>`, `cvc5 --tlimit <MILLISECONDS>`.
# 3. ADR-1957. A verdict NOTHING can check at the board budget is re-run against
#    both references at 600 s -- 25x -- and reported as confirmed, contradicted,
#    or STILL UNCONFIRMED, never folded into a zero.
#
# Usage: confirm-moved.sh <file-list> <bin> <arm-env-value> <cores> <out.tsv>
set -u
LIST="$1"; AX="$2"; ARMVAL="$3"; PIN="$4"; OUT="$5"
BUDGET=24
LONG=600
VLIM=$((8 * 1024 * 1024))
Z3=${Z3:-z3}
CVC5=${CVC5:-/nas3/data/axeyum/harness/bin/cvc5}

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

ax_run() {  # $1 = env value or "-" for the base arm
  local raw
  if [ "$1" = "-" ]; then
    raw=$(env -u AXEYUM_QUANT_EGRAPH_RESERVE timeout $((BUDGET + 16)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$2" 2>/dev/null)
  else
    raw=$(AXEYUM_QUANT_EGRAPH_RESERVE="$1" timeout $((BUDGET + 16)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$2" 2>/dev/null)
  fi
  printf '%s' "$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')"
}

printf 'file\tstatus\tbase_x3\tarm_x3\tz3_24\tcvc5_24\tz3_600\tcvc5_600\n' > "$OUT"
no_opinion=0
rows=0
while read -r f; do
  [ -z "$f" ] && continue
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  b=""; a=""
  for _ in 1 2 3; do b="$b,$(ax_run - "$f")"; a="$a,$(ax_run "$ARMVAL" "$f")"; done
  b=${b#,}; a=${a#,}
  z24=$(timeout 40 taskset -c "$PIN" "$Z3" -T:$BUDGET "$f" 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$')
  c24=$(timeout 40 taskset -c "$PIN" "$CVC5" --tlimit $((BUDGET * 1000)) "$f" 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$')
  z600="skipped"; c600="skipped"
  # Only spend 600 s where the board budget produced NO opinion at all: that is
  # exactly ADR-1957's case, and running it everywhere would cost hours for
  # rows already checked.
  # Written as three explicit `case`s rather than a chain of `[ ] || [ ] && [ ]`:
  # shell `&&`/`||` have EQUAL precedence and associate left to right, so the
  # obvious chain groups as `(a || b) && c` and silently asks a different
  # question. `no_opinion` is the ADR-1957 denominator -- the count of our
  # verdicts that NOTHING could compare against -- so getting it wrong is
  # exactly the vacuous zero that ADR forbids.
  opinion=0
  case "${st:-none}" in sat|unsat) opinion=1 ;; esac
  case "${z24:-none}" in sat|unsat) opinion=1 ;; esac
  case "${c24:-none}" in sat|unsat) opinion=1 ;; esac
  if [ "$opinion" -eq 0 ]; then
    z600=$(timeout $((LONG + 30)) taskset -c "$PIN" "$Z3" -T:$LONG "$f" 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$')
    c600=$(timeout $((LONG + 30)) taskset -c "$PIN" "$CVC5" --tlimit $((LONG * 1000)) "$f" 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$')
  fi
  rows=$((rows + 1))
  # ADR-1957's denominator, counted after the 600 s pass: a row nothing can
  # speak to at ANY budget.
  case "${z600:-none}${c600:-none}" in
    *sat*) ;;
    *) [ "$opinion" -eq 0 ] && no_opinion=$((no_opinion + 1)) ;;
  esac
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$f" "${st:-none}" "$b" "$a" "${z24:-none}" "${c24:-none}" "${z600:-none}" "${c600:-none}" >> "$OUT"
done < "$LIST"

echo "CONFIRM-DONE rows=$rows  NO-OPINION-AT-ANY-BUDGET=$no_opinion"
# This script MEASURES; `confirm-summarize.py` classifies and carries the
# finding-dependent exit status. Splitting them is not tidiness: the first
# version classified here and printed CONTRADICTED -- the word a soundness
# board is scanned for -- over rows where the arm had simply returned
# `unknown`. The raw per-run columns are what made that visible.
[ "$rows" -gt 0 ] || exit 2
exit 0
