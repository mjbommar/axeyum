#!/usr/bin/env bash
# The golden-Lean-module gate: run every suite that pins a rendered module's
# bytes, and refuse any new pin written the way the old ones were.
#
# WHY THIS EXISTS. Three times -- `0fc7cc357` (diagnosed by `6389e0194`),
# `b760fd6ae` (+863 bytes) and `46724faec` (+777 bytes) -- a commit changed the
# fixed MODULE BANNER that opens every rendered Lean module, re-pinned only the
# golden that happened to sit in a gate, and shipped the same delta unannounced
# onto every other golden. `main` was red for a day and the first ever completed
# run of `scripts/local-ci.sh` found it (artifacts/local-ci-runs/a6ee37c6a-s4.json,
# 4 failures in 7,511 tests, all one cause).
#
# Two things were wrong and this script is the second one's fix:
#
#   1. the pins covered the banner, so header text moved proof pins. Fixed at the
#      pin: `tests/support/lean_golden.rs` pins the module BODY and
#      `axeyum-lean-kernel --test module_banner_pin` pins the banner, once, as
#      committed text.
#   2. NOTHING RAN THESE SUITES. They are `tests/*.rs` integration targets;
#      `--lib` skips those by construction and `hooks/pre-push` names its suites
#      one at a time. The workspace has 465 integration suites and the pre-push
#      battery names six, so "add it to the hook" is the fix that already failed
#      -- `6389e0194` registered three of these four with
#      `scripts/check-lean-gate.sh`, which needs a real Lean binary and is not
#      what anyone runs before merging.
#
# So the membership is DISCOVERED, never listed. A suite is in this gate exactly
# when it calls `lean_golden::assert_golden_module`, which is the same act as
# being a golden pin. A new golden cannot be added outside the gate, and a hand-
# rolled whole-module pin that dodges the helper is refused below.
#
# Usage:
#   scripts/check-lean-golden-pins.sh            # discover, refuse, run
#   scripts/check-lean-golden-pins.sh --list     # discover and print only
set -uo pipefail
# The tree to scan and run in. Overridable so `scripts/tests/test-check-lean-golden-pins.sh`
# can point the SAME script at synthetic trees -- a gate whose guards are only
# ever exercised by the repository they guard has no failing case to show.
cd "${AXEYUM_GOLDEN_PIN_ROOT:-$(dirname "$0")/..}"

CARGO="${AXEYUM_CARGO:-cargo}"
list_only=0
[ "${1:-}" = "--list" ] && list_only=1

# --------------------------------------------------------------------------
# Discovery: package | test target | features
# --------------------------------------------------------------------------
suites=""
while IFS= read -r file; do
  pkg=$(printf '%s' "$file" | cut -d/ -f2)
  target=$(basename "$file" .rs)
  features=""
  grep -q '#!\[cfg(feature = "full")\]' "$file" && features="full"
  suites="${suites}${pkg}|${target}|${features}"$'\n'
done < <(grep -rl "assert_golden_module" crates/*/tests/*.rs 2>/dev/null | LC_ALL=C sort)

# The banner pin is the counterpart half and is always in the gate: it is the one
# place a header change is meant to be seen, so a green run without it would mean
# the golden bodies were checked and the text under all of them was not.
suites="${suites}axeyum-lean-kernel|module_banner_pin|"$'\n'

suite_count=$(printf '%s' "$suites" | grep -c .)
if [ "$suite_count" -lt 2 ]; then
  echo "check-lean-golden-pins: FAILED -- discovered $suite_count suites." \
       "Either every golden pin was deleted, or the helper was renamed and this" \
       "gate is now looking for a string nothing contains. A gate that discovers" \
       "nothing must fail, not pass." >&2
  exit 1
fi

# --------------------------------------------------------------------------
# Refusal: a whole-module byte pin that dodges the helper.
#
# The helper is what excludes the banner and what makes a suite discoverable
# above, so a hand-rolled `(source.len(), fnv1a)` over a rendered module puts a
# pin back under the banner AND outside this gate in one stroke -- which is
# exactly the state that shipped red three times.
# --------------------------------------------------------------------------
rc=0
FNV_OFFSET='0xcbf2_9ce4_8422_2325'
while IFS= read -r file; do
  grep -q "$FNV_OFFSET" "$file" || continue
  grep -q "assert_golden_module" "$file" && continue
  echo "check-lean-golden-pins: FAILED -- $file renders a Lean module and hashes" \
       "bytes with FNV-1a, but does not use \`lean_golden::assert_golden_module\`." \
       "A whole-module pin includes the shared banner, so header text moves it," \
       "and it is invisible to this gate. Use the helper (it pins the body and" \
       "still asserts the banner byte for byte), or hash something that is not a" \
       "rendered module." >&2
  rc=1
done < <(grep -rlE "_to_lean_module\(|render_lean_module" crates/*/tests/*.rs 2>/dev/null | LC_ALL=C sort)

printf '%-24s %-34s %-6s %8s  %s\n' PACKAGE SUITE FEATS TESTS RESULT
if [ "$list_only" = 1 ]; then
  while IFS='|' read -r pkg target features; do
    [ -n "$pkg" ] || continue
    printf '%-24s %-34s %-6s %8s  %s\n' "$pkg" "$target" "${features:--}" "-" "listed"
  done < <(printf '%s' "$suites")
else
  # ONE cargo invocation per (package, features) group, not one per suite: the
  # suites in a group share a build, and on this box every heavy cargo job takes
  # a host-wide flock (scripts/cargo-serialized.sh), so six invocations means six
  # queue waits behind whatever else the fleet is running. Grouped, this is one.
  groups=$(printf '%s' "$suites" | awk -F'|' 'NF{print $1"|"$3}' | LC_ALL=C sort -u)
  while IFS='|' read -r pkg features; do
    [ -n "$pkg" ] || continue
    targets=$(printf '%s' "$suites" | awk -F'|' -v p="$pkg" -v f="$features" '$1==p && $3==f {print $2}')
    args=(test --no-fail-fast -p "$pkg")
    [ -n "$features" ] && args+=(--features "$features")
    while IFS= read -r t; do [ -n "$t" ] && args+=(--test "$t"); done <<<"$targets"
    out=$("$CARGO" "${args[@]}" 2>&1)
    status=$?
    # Per-suite test COUNTS, not just the group's exit status. `cargo test` exits
    # 0 on an EMPTY test binary, so a `#![cfg(feature = ...)]` that empties one
    # suite of a green group is invisible by status alone -- the corpus sweep sat
    # inert that way for 15 days. cargo prints `Running tests/<name>.rs (...)`
    # before each binary's `running N tests`, so attribute the counts.
    counts=$(printf '%s\n' "$out" | awk '
      /^ *Running .*tests\// { sub(/^.*tests\//, "", $0); sub(/\.rs.*$/, "", $0); suite = $0; next }
      /^running [0-9]+ test/  { if (suite != "") { n[suite] += $2 } }
      END { for (s in n) print s"="n[s] }')
    while IFS= read -r t; do
      [ -n "$t" ] || continue
      ran=$(printf '%s\n' "$counts" | awk -F= -v s="$t" '$1==s {print $2}')
      ran=${ran:-0}
      if [ "$ran" -lt 1 ]; then
        printf '%-24s %-34s %-6s %8s  %s\n' "$pkg" "$t" "${features:--}" "$ran" "INERT"
        echo "check-lean-golden-pins: FAILED -- $pkg/$t ran ZERO tests. A feature" \
             "gate has emptied it, or it failed to build; either way this is inert," \
             "not passing." >&2
        rc=1
      elif [ "$status" -ne 0 ]; then
        # `--no-fail-fast` runs every suite, so one group failure does not say
        # WHICH suite; the transcript below does.
        printf '%-24s %-34s %-6s %8s  %s\n' "$pkg" "$t" "${features:--}" "$ran" "ran (group FAILED)"
      else
        printf '%-24s %-34s %-6s %8s  %s\n' "$pkg" "$t" "${features:--}" "$ran" "ok"
      fi
    done <<<"$targets"
    if [ "$status" -ne 0 ]; then
      printf '%s\n' "$out" | tail -60 >&2
      rc=1
    fi
  done <<<"$groups"
fi

if [ "$list_only" = 1 ]; then
  echo "check-lean-golden-pins: $suite_count golden-module suites discovered (not run)"
  exit "$rc"
fi
if [ "$rc" -eq 0 ]; then
  echo "check-lean-golden-pins: $suite_count golden-module suites green"
fi
exit "$rc"
