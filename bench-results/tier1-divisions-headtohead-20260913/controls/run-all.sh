#!/usr/bin/env bash
# Every control in this directory, plus the mutation table, in one command.
#
# It exists because five suites accumulated one at a time and re-running them
# by hand is how one gets forgotten -- and a forgotten control suite is
# indistinguishable from a passing one right up to the moment it matters.
#
# It reports the COUNT of suites it found and ran, derived from the directory
# rather than from a list here, so a suite added later cannot be silently
# skipped by a stale literal.  A test named "every X" must derive its X from the
# authority, not from the maintainer's memory.
set -u
cd "$(dirname "$0")"

mapfile -t SUITES < <(ls *-control.sh run-controls.sh 2>/dev/null | sort -u)
if [ "${#SUITES[@]}" -eq 0 ]; then
  echo "ABORT: no control suites found -- an empty run is not a pass"
  exit 2
fi

fail=0
for s in "${SUITES[@]}"; do
  printf '%-34s ' "$s"
  if out=$(bash "$s" 2>&1); then
    printf 'PASS  %s\n' "$(printf '%s' "$out" | tail -1)"
  else
    printf 'FAIL\n'
    printf '%s\n' "$out" | sed 's/^/    /'
    fail=1
  fi
done

printf '%-34s ' "mutants.py"
if out=$(python3 mutants.py 2>&1); then
  printf 'PASS  %s\n' "$(printf '%s' "$out" | tail -1)"
  printf '%-34s %s kill(s)\n' "" "$(printf '%s' "$out" | grep -c '^  kill ')"
else
  printf 'FAIL\n'
  printf '%s\n' "$out" | sed 's/^/    /'
  fail=1
fi

echo
if [ "$fail" = 0 ]; then
  echo "ALL-CONTROLS-OK: ${#SUITES[@]} suite(s) + the mutation table"
else
  echo "CONTROLS FAILED"
fi
exit "$fail"
