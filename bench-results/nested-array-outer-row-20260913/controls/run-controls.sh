#!/usr/bin/env bash
# The instrument's OWN controls.
#
# The AUFLIRA and AUFNIRA winnable lists refuse 187/187 and 139/139 under this
# surrogate (their files pass outer arrays to functions), so this instrument has
# NO natural population on which it is known to reach something.  Without that,
# a reach of 0 on ALIA is indistinguishable from an instrument that cannot reach
# anything -- the vacuous zero ADR-1957 warns about.
#
# These fixtures supply the missing opportunity.  Each is a nested-array query
# with a KNOWN verdict, inside the accepted fragment, and the expectation says
# which of the three things is being checked:
#
#   REACH   -- unsat, and its refutation NEEDS outer read-over-write.  axeyum
#              must answer `unsat` on the surrogate.  A `unknown` here means the
#              instrument is blind and every zero it reports is uninterpretable.
#   SAT     -- satisfiable.  axeyum must NOT answer `unsat` on the surrogate; if
#              it does, the rewrite is unsound in the direction the reach number
#              is read in, and the number is worthless.
#   REFUSE  -- outside the accepted fragment.  The script must say so rather
#              than rewrite it.
#   GAP     -- unsat, inside the fragment, and axeyum answers `unknown` TODAY.
#              A `sat` is a soundness defect and fails.  An `unsat` fails too,
#              loudly: the gap closed and ADR-1971's reach number is stale.
#
# Usage: run-controls.sh [budget_s]
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
BUDGET_S="${1:-24}"
AX="${AXEYUM_CLI:-/nas3/data/axeyum/harness/tier1-divisions/bin/smtcomp_cli}"
Z3="${Z3_BIN:-/usr/bin/z3}"
CVC5="${CVC5_BIN:-/nas3/data/axeyum/harness/bin/cvc5}"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

bad=0
printf '%-34s %-7s %-9s %-9s %-9s %-9s %s\n' \
  fixture kind ax_surr z3_surr z3_orig cvc5_orig result

for f in "$HERE"/*.smt2; do
  name="$(basename -- "$f" .smt2)"
  kind="$(grep -m1 -oE '; *EXPECT: *[A-Z]+' -- "$f" | awk '{print $3}')"
  tgt="$WORK/$name.smt2"
  if ! python3 "$HERE/../../../scripts/nested_array_outer_row_surrogate.py" "$f" "$tgt" 2> "$tgt.why"; then
    a="-"; zs="-"
    if [ "$kind" = "REFUSE" ]; then r=PASS; else r=FAIL; fi
  else
    a=$(timeout $((BUDGET_S * 2 + 10)) "$AX" "$tgt" --timeout-ms $((BUDGET_S * 1000)) 2>/dev/null \
          | grep -m1 -E '^(sat|unsat|unknown)$')
    zs=$(timeout $((BUDGET_S * 2 + 10)) "$Z3" -T:"$BUDGET_S" "$tgt" 2>/dev/null \
          | grep -m1 -E '^(sat|unsat|unknown)$')
    a="${a:-unknown}"; zs="${zs:-unknown}"
    case "$kind" in
      REACH)  [ "$a" = "unsat" ] && r=PASS || r=FAIL ;;
      SAT)    [ "$a" = "unsat" ] && r=FAIL || r=PASS ;;
      GAP)    case "$a" in
                unknown) r=PASS ;;
                unsat)   r="FAIL(GOOD NEWS: the gap closed, re-measure ADR-1971)" ;;
                *)       r="FAIL(WRONG VERDICT: this fixture is unsat)" ;;
              esac ;;
      REFUSE) r=FAIL ;;
      *)      r="FAIL(no EXPECT)" ;;
    esac
  fi
  zo=$(timeout $((BUDGET_S * 2 + 10)) "$Z3" -T:"$BUDGET_S" "$f" 2>/dev/null \
        | grep -m1 -E '^(sat|unsat|unknown)$')
  co=$(timeout $((BUDGET_S * 2 + 10)) "$CVC5" "--tlimit=$((BUDGET_S * 1000))" "$f" 2>/dev/null \
        | grep -m1 -E '^(sat|unsat|unknown)$')
  # The declared verdict is itself checked against both references on the
  # ORIGINAL, so a fixture cannot be wrong about its own subject.
  want=""
  case "$kind" in REACH) want=unsat ;; SAT) want=sat ;; esac
  for who in "${zo:-none}" "${co:-none}"; do
    if [ -n "$want" ] && [ "$who" != "$want" ] && [ "$who" != "unknown" ] && [ "$who" != "none" ]; then
      r="FAIL(reference says $who, fixture claims $want)"
    fi
  done
  [ "${r#PASS}" = "$r" ] && bad=$((bad + 1))
  printf '%-34s %-7s %-9s %-9s %-9s %-9s %s\n' \
    "$name" "$kind" "$a" "$zs" "${zo:-none}" "${co:-none}" "$r"
done

echo
if [ "$bad" -eq 0 ]; then
  echo "CONTROLS OK"
else
  echo "CONTROLS: $bad FAILURES"
fi
exit "$bad"
