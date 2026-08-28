#!/usr/bin/env bash
# Watch how expensive the `creal` prelude is to TYPE-CHECK, as a load-invariant
# ratio against a reference prelude build in the same binary.
#
# ## The failure this exists to convert
#
# `creal_prelude_builds` went 12.19 s -> 108.40 s in two days and nothing
# noticed, because the only thing watching it was a "94-123 s band" that lanes
# had established BY OBSERVING EACH OTHER during the window in which the
# regression was already underway. Every reading of "in band, no regression" was
# honest and locally correct; the aggregate was wrong. A tolerance derived from
# recent runs measures your recent runs.
# See docs/research/11-design-review/2026-08-28-the-band-is-the-regression.md.
#
# ## Why a ratio and not seconds
#
# Because a seconds budget on this box measures the queue, not the work.
# Measured 2026-08-28, same binary, same commit, one busy core pinned beside the
# test: absolute time moved 2.02x and the ratio moved 0.2%. The reference
# (`rat_prelude_builds`) is single-threaded kernel type-checking in the SAME
# binary as the subject, so contention scales both and divides out. The
# regression, meanwhile, moves the ratio 2.60 -> 20.21.
#
# ## Modes
#
#   --check     (default) Measure, compare against the pinned budget, and
#               RE-DEMONSTRATE that the verdict can go red -- against a halved
#               budget, and against a transcript reporting zero tests. A run
#               that has not observed its own guards fire has not shown it can
#               fail, so both demonstrations are required, not incidental.
#   --measure   Print a re-pinnable row. Same measurement, no budget applied.
#
# ## Env
#
#   AXEYUM_KERNEL_TEST_BIN     use this prebuilt test binary (takes no cargo
#                              lock -- the right tool when lanes are contending)
#   AXEYUM_CREAL_RATIO_PIN_FILE  read the budget from here instead of the
#                              tracked file, so the control suite can drive
#                              wrong pins WITHOUT mutating a tracked file that
#                              every other lane compiles from
#   AXEYUM_CREAL_RATIO_FAKE_SUBJECT / _REFERENCE
#                              read a canned harness transcript from this file
#                              instead of running the test, so the controls cost
#                              milliseconds instead of two minutes
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

PIN_FILE="${AXEYUM_CREAL_RATIO_PIN_FILE:-artifacts/creal-prelude-build-budget.tsv}"
MODE="check"

while [ $# -gt 0 ]; do
  case "$1" in
    --check)   MODE="check";   shift ;;
    --measure) MODE="measure"; shift ;;
    -h|--help) sed -n '2,45p' "$0"; exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

die() { echo "creal-build-ratio: $*" >&2; exit 1; }

# --- the pin ---------------------------------------------------------------
#
# `/usr/bin/grep` explicitly: interactively `grep` on this host is a shell
# function wrapping ugrep, which disagrees with GNU grep on escapes, and 68
# fact checkers were wrong because a pattern was validated in the wrong one.

[ -f "$PIN_FILE" ] || die "pin file not found: $PIN_FILE"
PIN_BODY="$(/usr/bin/grep -v '^#' "$PIN_FILE" | /usr/bin/grep -v '^subject' | /usr/bin/grep . || true)"
PIN_ROWS="$(printf '%s' "$PIN_BODY" | /usr/bin/grep -c . || true)"
[ "$PIN_ROWS" = "1" ] || die "expected exactly one pinned row in $PIN_FILE, found $PIN_ROWS"
read -r SUBJECT REFERENCE BUDGET <<<"$PIN_BODY"
[ -n "${SUBJECT:-}" ] && [ -n "${REFERENCE:-}" ] && [ -n "${BUDGET:-}" ] \
  || die "malformed pin row in $PIN_FILE"
awk -v b="$BUDGET" 'BEGIN { exit !(b + 0 > 0) }' \
  || die "pinned budget '$BUDGET' is not a positive number"

# --- the measurement -------------------------------------------------------

# The harness prints `... finished in Xs` on its summary line on STABLE rustc.
# `--report-time` (per-test times) needs nightly; this deliberately does not use
# it, so the gate runs everywhere CI does.
run_one() {
  local test_name="$1" fake="$2"
  if [ -n "$fake" ]; then
    cat "$fake"
    return 0
  fi
  "$TEST_BIN" --exact "$test_name" --test-threads=1 2>&1
}

# G1 vacuity: a filter that matches nothing prints `0 passed ... ok` and exits
# 0. That is the single most-repeated green-looking nothing in this repository,
# so the count is checked, not assumed.
# G2 parse: no `finished in` line means the transcript is not what we think it
# is; an unparsed number must never silently become 0.
extract_seconds() {
  local transcript="$1" who="$2" passed seconds
  passed="$(printf '%s\n' "$transcript" | /usr/bin/grep -cE '^test result: ok\. 1 passed;' || true)"
  [ "$passed" = "1" ] \
    || die "$who did not run exactly one passing test -- refusing to time a filter that matched nothing"
  seconds="$(printf '%s\n' "$transcript" \
    | /usr/bin/sed -nE 's/.*finished in ([0-9]+\.[0-9]+)s.*/\1/p' | tail -1)"
  [ -n "$seconds" ] \
    || die "$who printed no parsable 'finished in Xs' line"
  printf '%s' "$seconds"
}

FAKE_SUBJECT="${AXEYUM_CREAL_RATIO_FAKE_SUBJECT:-}"
FAKE_REFERENCE="${AXEYUM_CREAL_RATIO_FAKE_REFERENCE:-}"

if [ -z "$FAKE_SUBJECT" ] || [ -z "$FAKE_REFERENCE" ]; then
  TEST_BIN="${AXEYUM_KERNEL_TEST_BIN:-}"
  if [ -z "$TEST_BIN" ]; then
    echo "creal-build-ratio: building the debug lib test binary..." >&2
    TEST_BIN="$(scripts/cargo-serialized.sh test -p axeyum-lean-kernel --lib --no-run \
      --message-format=json 2>/dev/null \
      | python3 -c 'import json,sys
for line in sys.stdin:
    try:
        record = json.loads(line)
    except ValueError:
        continue
    if (record.get("reason") == "compiler-artifact"
            and record.get("target", {}).get("name") == "axeyum-lean-kernel"
            and record.get("profile", {}).get("test")
            and record.get("executable")):
        print(record["executable"])' | tail -1)"
  fi
  [ -n "$TEST_BIN" ] && [ -x "$TEST_BIN" ] || die "no kernel test binary (set AXEYUM_KERNEL_TEST_BIN)"
fi

# Reference FIRST: it is ~5% of the subject's cost, so a broken setup fails in
# seconds rather than after two minutes.
REF_T="$(extract_seconds "$(run_one "$REFERENCE" "$FAKE_REFERENCE")" "reference ($REFERENCE)")"
SUB_T="$(extract_seconds "$(run_one "$SUBJECT" "$FAKE_SUBJECT")" "subject ($SUBJECT)")"

# G3: a zero or absurdly small reference makes the ratio meaningless (and the
# division undefined). The reference builds a real prelude; under a second means
# something other than what we think ran.
awk -v r="$REF_T" 'BEGIN { exit !(r >= 1.0) }' \
  || die "reference measured ${REF_T}s -- under 1s it is not building the rat prelude, and the ratio would be noise"

RATIO="$(awk -v s="$SUB_T" -v r="$REF_T" 'BEGIN { printf "%.2f", s / r }')"

# --- the verdict, as a function so it can be re-run against a wrong budget ---

verdict() {  # $1 = ratio, $2 = budget; prints RED/GREEN, returns 1 on RED
  if awk -v x="$1" -v b="$2" 'BEGIN { exit !(x > b) }'; then
    echo RED
    return 1
  fi
  echo GREEN
}

echo "creal-build-ratio: subject ${SUB_T}s / reference ${REF_T}s = ${RATIO} (budget ${BUDGET})"

if [ "$MODE" = "measure" ]; then
  echo
  echo "re-pinnable row (the ratio rounded UP to the next whole unit, no further):"
  printf '%s\t%s\t%s\n' "$SUBJECT" "$REFERENCE" \
    "$(awk -v x="$RATIO" 'BEGIN { printf "%d", (x == int(x)) ? x : int(x) + 1 }')"
  exit 0
fi

# --- self-demonstration: this run must SHOW that it can fail ----------------
#
# Costs nothing: both demonstrations reuse the measurement already taken.

HALVED="$(awk -v b="$BUDGET" 'BEGIN { printf "%.4f", b / 2 }')"
if [ "$(verdict "$RATIO" "$HALVED" || true)" != "RED" ]; then
  die "SELF-CHECK FAILED: the budget comparison did not go RED at half the
  pinned budget (${HALVED}). A gate that has not been shown to fail is not a gate."
fi

ZERO_TESTS='
running 0 tests

test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 937 filtered out; finished in 0.00s
'
if (extract_seconds "$ZERO_TESTS" "self-check") >/dev/null 2>&1; then
  die "SELF-CHECK FAILED: a transcript reporting 0 tests was accepted. That is
  the green-looking nothing this repository has shipped more than once."
fi

echo "creal-build-ratio: self-check ok -- the verdict goes RED at half budget, and a zero-test transcript is rejected"

if verdict "$RATIO" "$BUDGET" >/dev/null; then
  echo "creal-build-ratio: GREEN -- ${RATIO} <= ${BUDGET}"
  exit 0
fi
echo "creal-build-ratio: RED -- ${RATIO} > ${BUDGET}" >&2
echo "  The creal prelude got more expensive to type-check RELATIVE to the rat" >&2
echo "  prelude, so this is not load. Find WHICH declaration with a per-step" >&2
echo "  timing pass over creal.rs's STEPS loop -- see" >&2
echo "  docs/plan/status/218-creal-build-bisect.md for the method and the" >&2
echo "  2026-08-28 distribution it produced." >&2
exit 1
