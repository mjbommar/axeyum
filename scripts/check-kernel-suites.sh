#!/usr/bin/env bash
# The kernel's push-time integration suites: run every `axeyum-lean-kernel`
# suite that does NOT need an external `lean`, and PROVE that the ones it skips
# are owned by `scripts/check-lean-gate.sh` rather than merely unrun.
#
# WHY THIS EXISTS. `hooks/pre-push` ran the crate WHOLESALE:
#
#     gated_test "kernel suites (unit + integration)" \
#       cargo test -p axeyum-lean-kernel --quiet
#
# That step is load-bearing and is not being removed: `cargo test --workspace
# --lib` runs unit tests only and skips every `tests/*.rs`, which is how
# `axeyum-lean-kernel --test axiom_footprint` sat RED on `main` for a day (a
# commit made `Int.euclidean_decomposition` a theorem and left three assertions
# still calling it an axiom). This is the crate where the trusted surface is
# asserted, so a stale assertion here is a stale claim about axiom-freedom.
#
# What was wrong is that the crate also holds fifteen suites that hand generated
# modules to a REAL `lean` binary, and `scripts/check-lean-gate.sh` already owns
# those -- it resolves the pinned toolchain, sets `AXEYUM_REQUIRE_LEAN=1`, counts
# the invocations and enforces a floor. So every push ran them a second time,
# with none of that accounting. The hook's comment said "~1.4s warm"; measured
# 2026-08-19 the step took 2,396 s of a 722-1,176 s hook, after two suites landed
# that morning (`real_lean_creal_carrier_kernel_replay` ~62 s and
# `real_lean_wellfounded_elaborator_divergence` ~115 s).
#
# MEMBERSHIP IS DISCOVERED, NEVER LISTED. A hand-written list of "the suites the
# hook runs" is a list someone forgets to extend, and the failure is silent: a
# new non-Lean suite simply never runs at push time. So the split is computed
# from the source, by the same act that makes a suite a real-Lean suite --
# `#[path = "support/lean_probe.rs"]`, the shared resolver every one of them uses
# and the thing that makes `AXEYUM_REQUIRE_LEAN=1` bite. (`check-lean-golden-pins.sh`
# discovers its membership the same way, from `assert_golden_module`.)
#
# And the partition is ASSERTED TOTAL, which is the part that makes this a gate
# rather than a convenience:
#
#     every crates/axeyum-lean-kernel/tests/*.rs is in EXACTLY ONE of
#       { runs here, at push time }  or  { owned by scripts/check-lean-gate.sh }
#
# A real-Lean suite absent from that gate's list fails HERE, by name -- it would
# otherwise be a suite that this script skips and nothing else runs, which is a
# strictly worse state than the duplication being removed. Running this for the
# first time on 2026-08-19 found exactly one:
# `real_lean_string_monoid_crosscheck`, live since 2026-08-17 and never in the
# real-Lean gate.
#
# Usage:
#   scripts/check-kernel-suites.sh          # partition, assert, run the push half
#   scripts/check-kernel-suites.sh --list   # partition and print only (no cargo)
#
# Controls (each guard driven to failure on a synthetic tree):
#   scripts/tests/test_check_kernel_suites.py
set -uo pipefail

# The tree to scan and run in. Overridable so the controls can point the SAME
# shipped script at synthetic trees -- a gate whose guards are only ever
# exercised by the repository they guard has no failing case to show.
cd "${AXEYUM_KERNEL_SUITES_ROOT:-$(dirname "$0")/..}" || exit 2

CARGO="${AXEYUM_CARGO:-cargo}"
PACKAGE="axeyum-lean-kernel"
TESTS_DIR="crates/$PACKAGE/tests"
LEAN_GATE="scripts/check-lean-gate.sh"
# The shared resolver. Using it IS being a real-Lean suite: it is what finds the
# pinned toolchain, what prints the `AXEYUM-LEAN-TOOLCHAIN` banner the real-Lean
# gate cross-checks, and what turns a missing binary into a failure under
# `AXEYUM_REQUIRE_LEAN=1`.
PROBE_MARKER='support/lean_probe.rs'

# `--no-lib` drops the crate's UNIT tests from the run. `hooks/pre-push` passes
# it because the step immediately above it there is `cargo test --workspace
# --lib`, which already runs them (the kernel has no cargo features, so the two
# select the same tests) -- and they are not cheap: several `creal_model` and
# `prelude_cache` unit tests run over 60 s each. Standalone, the default keeps
# them, so `scripts/check-kernel-suites.sh` on its own still means
# "this crate is green".
list_only=0
with_lib=1
for arg in "$@"; do
  case "$arg" in
    --list) list_only=1 ;;
    --no-lib) with_lib=0 ;;
    *) echo "check-kernel-suites: unknown argument '$arg'" >&2; exit 2 ;;
  esac
done

rc=0

# --------------------------------------------------------------------------
# Discovery
# --------------------------------------------------------------------------
all_suites=$(find "$TESTS_DIR" -maxdepth 1 -name '*.rs' -type f 2>/dev/null |
  sed 's#.*/##; s#\.rs$##' | LC_ALL=C sort)
all_count=$(printf '%s' "$all_suites" | grep -c . || true)

# A gate that discovers nothing must FAIL, not pass: "the crate has no suites"
# and "the path moved / the crate was renamed and this script is looking at an
# empty directory" are indistinguishable by exit status.
if [ "$all_count" -lt 2 ]; then
  echo "check-kernel-suites: FAILED -- discovered $all_count suite(s) under $TESTS_DIR." \
       "Either every integration suite was deleted, or this script is pointed at the" \
       "wrong tree. A gate that discovers nothing must fail, not pass." >&2
  exit 1
fi

lean_suites=$(grep -lF "$PROBE_MARKER" "$TESTS_DIR"/*.rs 2>/dev/null |
  sed 's#.*/##; s#\.rs$##' | LC_ALL=C sort)
push_suites=$(LC_ALL=C comm -23 <(printf '%s\n' "$all_suites") <(printf '%s\n' "$lean_suites"))
lean_count=$(printf '%s' "$lean_suites" | grep -c . || true)
push_count=$(printf '%s' "$push_suites" | grep -c . || true)

# What the real-Lean gate says it owns, read out of the gate itself rather than
# copied. Its suite table is `package|features|target`, one per line.
gate_suites=$(grep -E "^$PACKAGE\|" "$LEAN_GATE" 2>/dev/null |
  cut -d'|' -f3 | LC_ALL=C sort -u)
gate_count=$(printf '%s' "$gate_suites" | grep -c . || true)

# Fail-closed on the parse. If the table's format changes, `gate_suites` goes
# empty and EVERY real-Lean suite reads as unowned below -- which is the right
# answer but the wrong explanation, and the fix would be looked for in the wrong
# file. Say what actually happened.
#
# Conditioned on there being something to own: a crate with no real-Lean suite at
# all needs no table, and firing here would make this guard indistinguishable
# from the discovery guard above.
if [ "$gate_count" -eq 0 ] && [ "$lean_count" -gt 0 ]; then
  echo "check-kernel-suites: FAILED -- $lean_count suite(s) here use $PROBE_MARKER but this" \
       "script read ZERO $PACKAGE suites out of $LEAN_GATE." \
       "Its 'package|features|target' table is what tells this script which suites are" \
       "owned elsewhere; unreadable, that ownership cannot be checked at all." >&2
  exit 1
fi

# --------------------------------------------------------------------------
# The partition must be TOTAL and DISJOINT.
#
# Three ways it can break, each named separately because each has a different
# fix: a real-Lean suite nobody owns; an owned suite that no longer exists; and
# an owned suite that does not actually use the probe (so it would run in BOTH
# halves, which is the duplication this script exists to remove).
# --------------------------------------------------------------------------
while IFS= read -r suite; do
  [ -n "$suite" ] || continue
  if ! printf '%s\n' "$gate_suites" | grep -qxF "$suite"; then
    echo "check-kernel-suites: FAILED -- $suite uses $PROBE_MARKER (it invokes a real" \
         "\`lean\`) but $LEAN_GATE does not list it. This script skips it, so nothing would" \
         "run it: its Lean checks would not reach that gate's count or its floor. Add" \
         "'$PACKAGE||$suite' to the suites table there and raise CHECK_FLOOR by what it" \
         "checks." >&2
    rc=1
  fi
done <<<"$lean_suites"

while IFS= read -r suite; do
  [ -n "$suite" ] || continue
  if [ ! -f "$TESTS_DIR/$suite.rs" ]; then
    echo "check-kernel-suites: FAILED -- $LEAN_GATE lists $PACKAGE/$suite, but" \
         "$TESTS_DIR/$suite.rs does not exist. That gate would fail on it too, later and" \
         "more expensively; a renamed or deleted suite must be removed from the table." >&2
    rc=1
    continue
  fi
  if ! printf '%s\n' "$lean_suites" | grep -qxF "$suite"; then
    echo "check-kernel-suites: FAILED -- $LEAN_GATE lists $PACKAGE/$suite, but that suite" \
         "does not use $PROBE_MARKER, so it needs no external \`lean\` and this script would" \
         "run it as well. One suite in both halves is the duplication this split removes." \
         "Either use the probe or drop it from that table." >&2
    rc=1
  fi
done <<<"$gate_suites"

# --------------------------------------------------------------------------
# Refusal: a suite that resolves its own `lean` instead of using the probe.
#
# Discovery above keys on the probe, so a hand-rolled resolver puts a suite
# OUTSIDE the real-Lean gate and INSIDE the push half in one stroke -- a real
# `lean` invocation on every push, uncounted, unpinned, and free to take a silent
# skip path when the binary is missing. That is the 2026-08-14 incident
# (`a5975725f`) with the accounting removed.
# --------------------------------------------------------------------------
while IFS= read -r file; do
  [ -n "$file" ] || continue
  grep -qF "$PROBE_MARKER" "$file" && continue
  echo "check-kernel-suites: FAILED -- $file resolves a \`lean\` binary of its own instead" \
       "of using $PROBE_MARKER. Then it is invisible to $LEAN_GATE (which counts checks," \
       "enforces the pin and forbids skips) and would run a real Lean on every push" \
       "instead. Use the probe." >&2
  rc=1
done < <(grep -lE 'AXEYUM_LEAN_BIN|Command::new\("lean"\)|elan' "$TESTS_DIR"/*.rs 2>/dev/null |
  LC_ALL=C sort)

# --------------------------------------------------------------------------
# Refusal: a real-Lean suite that reports its check count by hand.
#
# `scripts/check-lean-gate.sh` parses exactly `AXEYUM-LEAN-CHECKED <tag>
# checked=<n>` and sums it against a floor, so a marker line in any other shape
# reads as ZERO -- the suite is listed, runs, invokes Lean, and contributes
# nothing to the number the gate enforces. `real_lean_string_monoid_crosscheck`
# printed `AXEYUM-LEAN-CHECKED|string-monoid|1|...` from 2026-08-17 until this
# guard was written, so listing it there without noticing would have swapped one
# silent hole for another. `lean_probe::report_checked` emits the parsed shape
# AND refuses a zero count.
# --------------------------------------------------------------------------
while IFS= read -r file; do
  [ -n "$file" ] || continue
  grep -q 'report_checked' "$file" && continue
  echo "check-kernel-suites: FAILED -- $file writes the CHECKED_MARKER line itself instead" \
       "of calling \`lean_probe::report_checked\`. $LEAN_GATE parses one exact shape" \
       "(\`AXEYUM-LEAN-CHECKED <tag> checked=<n>\`); anything else sums as zero, so the" \
       "suite's Lean invocations would never reach its floor." >&2
  rc=1
done < <(grep -lF 'CHECKED_MARKER' "$TESTS_DIR"/*.rs 2>/dev/null | LC_ALL=C sort)

# Everything deferred and nothing run is not a split, it is a deletion.
if [ "$push_count" -eq 0 ]; then
  echo "check-kernel-suites: FAILED -- every one of the $all_count suites was classified as" \
       "real-Lean, so this step would run NOTHING at push time. \`axiom_footprint\` and the" \
       "other trusted-surface assertions are exactly what must not be deferred to a gate" \
       "that needs a toolchain." >&2
  rc=1
fi

echo "check-kernel-suites: $all_count suites under $TESTS_DIR --" \
     "$push_count run here, $lean_count owned by $LEAN_GATE"

if [ "$list_only" = 1 ]; then
  printf '%-52s %s\n' SUITE HALF
  while IFS= read -r suite; do
    [ -n "$suite" ] && printf '%-52s %s\n' "$suite" "push"
  done <<<"$push_suites"
  while IFS= read -r suite; do
    [ -n "$suite" ] && printf '%-52s %s\n' "$suite" "check-lean-gate.sh"
  done <<<"$lean_suites"
  exit "$rc"
fi

[ "$rc" -ne 0 ] && exit 1

# --------------------------------------------------------------------------
# Run the push half: the lib unit tests plus every non-Lean integration suite,
# in ONE cargo invocation (they share a build, and every heavy cargo job on this
# box takes a host-wide semaphore, so N invocations means N queue waits).
#
# `--no-fail-fast` so one red suite does not hide the rest, and PER-SUITE test
# counts rather than the group's exit status: `cargo test` exits 0 on an empty
# test binary, which is how the corpus sweep sat inert for 15 days.
# --------------------------------------------------------------------------
# NOT `-q`: the per-suite attribution below reads cargo's `Running tests/<name>.rs`
# headers, and `--quiet` suppresses them -- the counts would all land on nothing
# and every suite would read as INERT.
args=(test --no-fail-fast -p "$PACKAGE")
[ "$with_lib" = 1 ] && args+=(--lib)
while IFS= read -r suite; do
  [ -n "$suite" ] && args+=(--test "$suite")
done <<<"$push_suites"

out=$("$CARGO" "${args[@]}" 2>&1)
status=$?

# cargo prints `Running tests/<name>.rs (...)` (and `Running unittests src/lib.rs
# (...)`) before each binary's `running N tests`, so the counts can be attributed
# to the target that produced them.
counts=$(printf '%s\n' "$out" | awk '
  /^ *Running unittests/          { target = "--lib"; next }
  /^ *Running .*tests\//          { sub(/^.*tests\//, "", $0); sub(/\.rs.*$/, "", $0); target = $0; next }
  /^running [0-9]+ test/          { if (target != "") { n[target] += $2 } }
  END { for (t in n) print t"="n[t] }')

suite_ran() { printf '%s\n' "$counts" | awk -F= -v s="$1" '$1==s {print $2}'; }

total_tests=0
targets_run=$(printf '%s\n' "$push_suites")
[ "$with_lib" = 1 ] && targets_run="--lib"$'\n'"$targets_run"
printf '%-52s %8s  %s\n' SUITE TESTS RESULT
for target in $targets_run; do
  [ -n "$target" ] || continue
  ran=$(suite_ran "$target")
  ran=${ran:-0}
  total_tests=$((total_tests + ran))
  if [ "$ran" -lt 1 ]; then
    printf '%-52s %8s  %s\n' "$target" "$ran" "INERT"
    echo "check-kernel-suites: FAILED -- $PACKAGE/$target ran ZERO tests. A feature gate has" \
         "emptied it, or it failed to build; either way this is inert, not passing." >&2
    rc=1
  elif [ "$status" -ne 0 ]; then
    printf '%-52s %8s  %s\n' "$target" "$ran" "ran (group FAILED)"
  else
    printf '%-52s %8s  %s\n' "$target" "$ran" "ok"
  fi
done

if [ "$status" -ne 0 ]; then
  printf '%s\n' "$out" | tail -60 >&2
  echo "check-kernel-suites: FAILED -- the push half of $PACKAGE is red." >&2
  rc=1
fi

if [ "$rc" -eq 0 ]; then
  lib_note="+ lib"
  [ "$with_lib" = 1 ] || lib_note="(--no-lib: unit tests left to the workspace --lib sweep)"
  echo "check-kernel-suites: OK -- $push_count suites $lib_note, $total_tests tests." \
       "The other $lean_count are real-Lean suites and run under $LEAN_GATE" \
       "(NOT skipped silently: they are checked there, with a counted floor)."
fi
exit "$rc"
