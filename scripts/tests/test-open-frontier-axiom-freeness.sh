#!/usr/bin/env bash
# Controls for `scripts/check-autogenesis-open-frontier-axiom-freeness.py`.
#
# One case per guard, and each case asserts the SPECIFIC error line that guard
# emits -- so deleting any single guard kills exactly the case that names it,
# and a case cannot be satisfied by some other guard rejecting first.  The
# baseline case is what makes the whole suite non-vacuous: it fails if the
# checker rejects the committed census.
set -u

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
CHECK="$ROOT/scripts/check-autogenesis-open-frontier-axiom-freeness.py"
CENSUS="$ROOT/artifacts/autogenesis/open-frontier-axiom-freeness-census-v1.json"
NURSERY="$ROOT/artifacts/autogenesis/nursery-v1.json"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

failures=0
ran=0

# run_case <name> <expect-exit> <expect-substring-or-empty> <python-mutator>
run_case() {
  local name="$1" expect="$2" needle="$3" mutator="$4"
  ran=$((ran + 1))
  local target="$WORK/$name.json"
  if [ -z "$mutator" ]; then
    cp "$CENSUS" "$target"
  else
    CENSUS_IN="$CENSUS" CENSUS_OUT="$target" NURSERY="$NURSERY" \
      python3 -c "$mutator" || { echo "FAIL[$name] mutator errored"; failures=$((failures + 1)); return; }
  fi
  local out status
  out="$(python3 "$CHECK" --census "$target" 2>&1)"
  status=$?
  if [ "$status" -ne "$expect" ]; then
    echo "FAIL[$name] exit=$status expected=$expect"
    echo "$out" | sed 's/^/    /'
    failures=$((failures + 1))
    return
  fi
  if [ -n "$needle" ] && ! printf '%s\n' "$out" | grep -qF -- "$needle"; then
    echo "FAIL[$name] output did not name its own guard: $needle"
    echo "$out" | sed 's/^/    /'
    failures=$((failures + 1))
    return
  fi
  echo "ok[$name]"
}

PRE='
import json, os
c = json.load(open(os.environ["CENSUS_IN"]))
'
POST='
json.dump(c, open(os.environ["CENSUS_OUT"], "w"), indent=2, sort_keys=True)
'

# The committed census must pass. Without this, every case below could be
# satisfied by a checker that rejects everything.
run_case baseline-passes 0 "verdict=PASS" ""

run_case absent-fact 1 "row names an absent fact" "$PRE
c['rows'][0]['fact_id'] = 'F:this-fact-does-not-exist'
$POST"

run_case held-out-row 1 "row names a HELD-OUT fact" "$PRE
held = [e['fact_id'] for e in json.load(open(os.environ['NURSERY']))['entries'] if e.get('partition') == 'held-out']
c['rows'][0]['fact_id'] = held[0]
$POST"

run_case count-mismatch 1 "but rows say" "$PRE
c['population']['axiom_bearing'] = c['population']['axiom_bearing'] + 1
$POST"

run_case axiom-free-list-drift 1 "axiom_free_declarations" "$PRE
c['axiom_free_declarations'] = sorted(c['axiom_free_declarations'] + ['Nat.not_measured_here'])
$POST"

run_case coverage-gap 1 "absent from the census" "$PRE
keep = [r for r in c['rows'] if r['resolved']]
drop = keep[0]
c['rows'] = [r for r in c['rows'] if r is not drop]
res = [r for r in c['rows'] if r['resolved']]
free = [r for r in res if r['lean_axiom_footprint'] == []]
c['population'].update(total=len(c['rows']), resolved_in_mathlib=len(res),
                       unresolved_in_mathlib=len(c['rows']) - len(res),
                       axiom_free=len(free), axiom_bearing=len(res) - len(free))
c['axiom_free_declarations'] = sorted(r['declaration'] for r in free)
$POST"

run_case vacuous-all-axiom-free 1 "did not discriminate" "$PRE
for r in c['rows']:
    if r['resolved']:
        r['lean_axiom_footprint'] = []
res = [r for r in c['rows'] if r['resolved']]
c['population'].update(axiom_free=len(res), axiom_bearing=0)
c['axiom_free_declarations'] = sorted(r['declaration'] for r in res)
$POST"

echo "cases=$ran failures=$failures"
[ "$ran" -ge 7 ] || { echo "FAIL: suite ran $ran cases; it must run every registered case"; exit 1; }
[ "$failures" -eq 0 ] || exit 1
