#!/usr/bin/env bash
# Controls for `scripts/new-fact.py` — the scaffolder that is supposed to make a
# fact's evidence PROVE it can fail before the fact exists.
#
# The thing being controlled is a checker for checkers, so the way it fails is
# by being agreeable. Each case below is a pattern that must be REFUSED, plus
# the round trip that matters: the `checker_command` it emits is run for real,
# against the true output and against mutated output, and must exit 0 and
# non-zero respectively. A scaffolder whose emitted command does not
# discriminate has produced exactly the artefact it exists to prevent.
#
# Case 4 is the one that found a real defect. The first version validated
# patterns with Python's `re` while emitting `grep -E`, and those engines
# disagree on `[[:space:]]` — a POSIX class to grep, a nested set to `re`, which
# warns and matches something else. It rejected a pattern grep accepts: a
# checker for checkers, checking a different language from the one that ships.
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
fail=0
ok()   { echo "ok   $1"; }
bad()  { echo "FAIL $1"; fail=1; }

# A fixture with a verdict, a pinned count, and prose that mentions neither.
printf 'widget report\nrows: 5 total\nall ok: true\n' > "$WORK/out"
CMD="cat $WORK/out"
BASE=(python3 scripts/new-fact.py --id F:zz-control --title t --statement s --date 2026-08-18)

run() { "${BASE[@]}" --command "$CMD" "$@" 2>&1; }

# --- 1. prose that no mutation touches is REFUSED --------------------------
if out=$(run --require 'widget report'); then
  bad "1 non-discriminating pattern was ACCEPTED"
else
  case "$out" in *"survives EVERY mutation"*) ok "1 non-discriminating pattern refused" ;;
    *) bad "1 refused, but not for the discrimination reason: $out" ;; esac
fi

# --- 2. a pattern matching nothing is REFUSED ------------------------------
if out=$(run --require '^no such line$'); then
  bad "2 a pattern matching nothing was ACCEPTED"
else
  case "$out" in *"matches NOTHING"*) ok "2 never-true pattern refused" ;;
    *) bad "2 refused, but not for the never-true reason" ;; esac
fi

# --- 3. population-only is refused, and the flag is what allows it ---------
if out=$(run --require-count '^rows: [0-9]+ total$=1'); then
  bad "3 population-only pattern was ACCEPTED without the flag"
else
  case "$out" in *"POPULATION-ONLY"*) ok "3 population-only refused without the flag" ;;
    *) bad "3 refused, but not as population-only" ;; esac
fi
if run --require-count '^rows: [0-9]+ total$=1' --allow-population-only >/dev/null; then
  ok "3b --allow-population-only accepts it"
else
  bad "3b the flag did not accept a population-only pattern"
fi

# --- 4. a POSIX class must be validated by GREP's engine, not Python's -----
# `[[:space:]]` is why this case exists; see the header.
if run --require '^all[[:space:]]ok: true$' >/dev/null 2>&1; then
  ok "4 POSIX character class accepted (validated with grep -E)"
else
  bad "4 a pattern grep -E accepts was refused -- wrong regex engine"
fi

# --- 5. THE ROUND TRIP: the emitted command discriminates for real ---------
"${BASE[@]}" --command "$CMD" --require '^all ok: true$' \
  --require-count '^rows: 5 total$=1' --write >/dev/null 2>&1
emitted="artifacts/facts/F-zz-control.json"
if [ ! -f "$emitted" ]; then
  bad "5 nothing was written, so the round trip cannot be tested"
else
  n=0; pass=0; discriminated=0
  while IFS= read -r cmd; do
    n=$((n + 1))
    bash -c "$cmd" >/dev/null 2>&1 && pass=$((pass + 1))
    # Now break the finding and require the SAME command to fail.
    printf 'widget report\nrows: 6 total\nall ok: false\n' > "$WORK/out"
    bash -c "$cmd" >/dev/null 2>&1 || discriminated=$((discriminated + 1))
    printf 'widget report\nrows: 5 total\nall ok: true\n' > "$WORK/out"
  done < <(python3 -c '
import json, sys
d = json.load(open("artifacts/facts/F-zz-control.json"))
for e in d["evidence"]:
    print(e["checker_command"])
')
  rm -f "$emitted"
  [ "$n" -ge 2 ] || bad "5 expected 2 emitted commands, got $n"
  [ "$pass" = "$n" ] && ok "5 all $n emitted commands pass on the true output" \
    || bad "5 only $pass of $n emitted commands passed on the true output"
  [ "$discriminated" = "$n" ] && ok "5b all $n emitted commands FAIL on mutated output" \
    || bad "5b only $discriminated of $n emitted commands failed on mutated output"
fi

if [ "$fail" = 0 ]; then echo "NEW_FACT_CONTROLS|ok"; else echo "NEW_FACT_CONTROLS|FAILED" >&2; fi
exit "$fail"
