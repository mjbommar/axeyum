#!/usr/bin/env bash
# ABC bit-blasting cross-check gate — roadmap item 2.4
# (docs/solver-comparison-2026-09/11-roadmap-and-plan.md).
#
# `docs/solver-comparison-2026-09/09-abc-and-aiger.md` found that axeyum's AIG
# export (`Aig::to_aiger_ascii`, `crates/axeyum-aig/src/lib.rs:628`) writes
# ASCII AIGER while ABC's own readers accept binary AIGER only
# (`giaAiger.c:1980`), and that the AIGER project's own `aigtoaig` converts
# ASCII to binary in one hop. `crates/axeyum-solver/tests/abc_crosscheck.rs`
# is that hop wired to a real check: two independently-built circuits for the
# same Boolean function are exported, converted, and handed to ABC's `&cec`
# (combinational equivalence checker).
#
# Both `abc` and `aigtoaig` are OPTIONAL, external, gitignored dependencies —
# neither is vendored, and **ABC is never built by this script or by the test
# suite**: it is a 56 MB, ~1.1M-line C application (see the module doc on the
# Rust suite for the full reasoning). `aigtoaig` is two small C files and IS
# safe to build automatically, mirroring how `scripts/fetch-references.sh`
# builds `drat-trim` from source.
#
# So, by design, and unlike `check-carcara-gate.sh` (which fails by default
# when its binary is absent): this gate SKIPS when `abc` cannot be found, and
# only turns that into a FAILURE when `AXEYUM_REQUIRE_ABC=1` — exactly the
# "Optional dependency; skip-and-fail under AXEYUM_REQUIRE_ABC=1" exit
# criterion in the roadmap. The Rust suite still runs its ABC-independent
# checks (brute-force `Aig::eval` semantic equivalence, ASCII AIGER
# well-formedness, and — when `aigtoaig` is available — a real binary AIGER
# conversion) in every mode, so an absent `abc` never means "nothing ran".
#
# The one thing this gate does NOT do differently from Carcara's: trust ABC's
# exit status. `abc -q "&cec f1 f2"` (`references/abc/src/base/main/
# mainReal.c:389`) returns 0 from `Abc_RealMain` whether the networks are
# equivalent, inequivalent, or undecided — the verdict is parsed from stdout
# text by `abc_verdict()` in the Rust suite, never from `$?`. See that
# function's doc comment for the exact strings and their source citations.
#
# Usage:
#   scripts/check-abc-crosscheck.sh                 # resolve, run, report
#   AXEYUM_REQUIRE_ABC=1 scripts/check-abc-crosscheck.sh   # fail if abc absent
#   scripts/check-abc-crosscheck.sh --self-check     # bash-only verdict-string
#                                                     # parser check, no cargo
#   scripts/check-abc-crosscheck.sh --print-bin      # resolve and print, run nothing
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2

SUITE_PACKAGE="axeyum-solver"
SUITE_TARGET="abc_crosscheck"

# ---------------------------------------------------------------------------
# Binary resolution.
# ---------------------------------------------------------------------------

resolve_abc() {
  if [ -n "${AXEYUM_ABC_BIN:-}" ]; then
    if [ -x "$AXEYUM_ABC_BIN" ]; then
      printf '%s\n' "$AXEYUM_ABC_BIN"
      return 0
    fi
    echo "check-abc-crosscheck: AXEYUM_ABC_BIN=$AXEYUM_ABC_BIN is not executable." >&2
    return 1
  fi
  if [ -x "references/abc/abc" ]; then
    printf '%s\n' "references/abc/abc"
    return 0
  fi
  local on_path
  on_path=$(command -v abc 2>/dev/null) || true
  if [ -n "$on_path" ]; then
    printf '%s\n' "$on_path"
    return 0
  fi
  return 1
}

# `aigtoaig` is small and safe to build from source (two C files, no
# dependency beyond `aiger.c`/`aiger.h`) — unlike `abc`, which this script
# NEVER builds. Builds into the reference clone's own directory so a repeat
# run finds it without rebuilding.
resolve_or_build_aigtoaig() {
  if [ -n "${AXEYUM_AIGTOAIG_BIN:-}" ]; then
    if [ -x "$AXEYUM_AIGTOAIG_BIN" ]; then
      printf '%s\n' "$AXEYUM_AIGTOAIG_BIN"
      return 0
    fi
    echo "check-abc-crosscheck: AXEYUM_AIGTOAIG_BIN=$AXEYUM_AIGTOAIG_BIN is not executable." >&2
    return 1
  fi
  if [ -x "references/aiger/aigtoaig" ]; then
    printf '%s\n' "references/aiger/aigtoaig"
    return 0
  fi
  local on_path
  on_path=$(command -v aigtoaig 2>/dev/null) || true
  if [ -n "$on_path" ]; then
    printf '%s\n' "$on_path"
    return 0
  fi
  if [ -f "references/aiger/aigtoaig.c" ] && [ -f "references/aiger/aiger.c" ]; then
    echo "check-abc-crosscheck: building aigtoaig from references/aiger (tiny, two C files)..." >&2
    if cc -O2 -o "references/aiger/aigtoaig" \
         "references/aiger/aigtoaig.c" "references/aiger/aiger.c"; then
      printf '%s\n' "references/aiger/aigtoaig"
      return 0
    fi
    echo "check-abc-crosscheck: building aigtoaig FAILED." >&2
    return 1
  fi
  return 1
}

abc=$(resolve_abc) || abc=""
aigtoaig=$(resolve_or_build_aigtoaig) || aigtoaig=""

if [ "${1:-}" = "--print-bin" ]; then
  printf 'abc\t%s\n' "${abc:-<none>}"
  printf 'aigtoaig\t%s\n' "${aigtoaig:-<none>}"
  exit 0
fi

# ---------------------------------------------------------------------------
# --self-check: the gate's own negative control for the verdict PARSER, no
# cargo build and no real abc/aigtoaig required. Mirrors
# check-carcara-gate.sh's --self-check.
# ---------------------------------------------------------------------------
if [ "${1:-}" = "--self-check" ]; then
  # These are the literal lines `Cec_ManVerify` prints, measured from the ABC
  # clone at fbaae01487b05982739a5636df30687f41a10a2d on 2026-09-09
  # (references/abc/src/proof/cec/cecCec.c:190, :198, :225). The Rust parser
  # (`abc_verdict` in abc_crosscheck.rs) is pinned against exactly these
  # strings by `abc_verdict_parses_measured_strings`; this shell version
  # exists so the classification can be demonstrated WITHOUT a cargo build,
  # matching the "cannot run ABC, still demonstrate what you can" instruction.
  self_fail=0
  classify() {
    case "$1" in
      *"NOT EQUIVALENT"*) echo "not-equivalent" ;;
      *"UNDECIDED"*) echo "undecided" ;;
      *"Networks are equivalent."*) echo "equivalent" ;;
      *) echo "unparsed" ;;
    esac
  }
  for case in \
    "Networks are equivalent.  Time = 0.00 sec|equivalent" \
    "Networks are NOT EQUIVALENT.  Time = 0.00 sec|not-equivalent" \
    "Networks are UNDECIDED.  Time = 0.00 sec|undecided" \
    "garbage, no verdict line|unparsed"; do
    line="${case%%|*}"
    want="${case##*|}"
    got=$(classify "$line")
    if [ "$got" != "$want" ]; then
      echo "check-abc-crosscheck --self-check: line '$line' classified as '$got', expected '$want'" >&2
      self_fail=1
    else
      printf 'check-abc-crosscheck --self-check: %-55s -> %s\n' "$line" "$got"
    fi
  done
  # The load-bearing case: a NOT-EQUIVALENT line must never classify as
  # equivalent, even though it contains "EQUIVALENT" as a substring.
  not_equiv_class=$(classify "Networks are NOT EQUIVALENT.  Time = 0.00 sec")
  if [ "$not_equiv_class" = "equivalent" ]; then
    echo "check-abc-crosscheck --self-check: THE SUBSTRING TRAP FIRED -- a NOT EQUIVALENT line" \
         "classified as equivalent." >&2
    self_fail=1
  fi
  if [ "$self_fail" -ne 0 ]; then
    echo "check-abc-crosscheck --self-check: FAILED"
    exit 1
  fi
  echo "check-abc-crosscheck --self-check: OK -- verdict-string classification matches the" \
       "literal strings measured from ABC's source, and the NOT-EQUIVALENT/equivalent" \
       "substring trap does not fire."
  exit 0
fi

# ---------------------------------------------------------------------------
# The gate proper.
# ---------------------------------------------------------------------------
if [ -z "$abc" ]; then
  if [ "${AXEYUM_REQUIRE_ABC:-}" = "1" ]; then
    cat >&2 <<'NOBIN'
check-abc-crosscheck: FAILED -- no `abc` binary, and AXEYUM_REQUIRE_ABC=1.

This is a FAILURE and not a skip on purpose (roadmap item 2.4's exit
criterion: "skip-and-fail under AXEYUM_REQUIRE_ABC=1"). To fix, either point
at a binary:

    AXEYUM_ABC_BIN=/path/to/abc scripts/check-abc-crosscheck.sh

...or place one at references/abc/abc, or put `abc` on PATH.

Do NOT build ABC from source as part of provisioning this gate -- it is a
56 MB, ~1.1M-line C application (references/abc, clone
fbaae01487b05982739a5636df30687f41a10a2d), and building it is explicitly out
of scope for this gate (docs/solver-comparison-2026-09/11-roadmap-and-plan.md
"Do not add a reference solver as a dependency" rule). Provision it
out-of-band on a host that is supposed to run this gate for real.
NOBIN
    exit 1
  fi
  echo "check-abc-crosscheck: no \`abc\` binary found -- SKIPPING the ABC-backed half of" \
       "the cross-check (optional dependency). Running the suite's ABC-independent checks" \
       "(semantic equivalence via Aig::eval, ASCII AIGER well-formedness, and binary AIGER" \
       "conversion${aigtoaig:+ via $aigtoaig}) so this is not a silent no-op." >&2
else
  echo "check-abc-crosscheck: using abc at $abc"
fi
if [ -z "$aigtoaig" ]; then
  echo "check-abc-crosscheck: no \`aigtoaig\` binary found or buildable -- binary AIGER" \
       "conversion will not be exercised this run." >&2
else
  echo "check-abc-crosscheck: using aigtoaig at $aigtoaig"
fi

export AXEYUM_ABC_BIN="$abc"
export AXEYUM_AIGTOAIG_BIN="$aigtoaig"

log=$(mktemp) || exit 2
trap 'rm -f "$log"' EXIT

args=(test -q -p "$SUITE_PACKAGE" --test "$SUITE_TARGET" -- --nocapture)
if ! cargo "${args[@]}" >"$log" 2>&1; then
  echo "check-abc-crosscheck: SUITE FAILED" >&2
  cat "$log" >&2
  exit 1
fi

tests=$(sed -n 's/^running \([0-9]*\) test.*/\1/p' "$log" | awk '{s+=$1} END {print s+0}')
if [ "$tests" = "0" ]; then
  echo "check-abc-crosscheck: $SUITE_TARGET compiled to ZERO tests -- the 'running 0 tests" \
       "... ok' trap. Something is wrong with how this gate invoked cargo." >&2
  cat "$log" >&2
  exit 1
fi

# NOT anchored with `^`: cargo's default parallel test harness prefixes each
# completed test with a `.` progress character, glued directly onto the next
# line's captured stdout under `-q -- --nocapture` -- measured 2026-09-09,
# e.g. `.AXEYUM-ABC-SEMANTIC-CHECK ...`. An anchored pattern silently matched
# zero lines here despite the suite genuinely printing them; same trap this
# repository's CLAUDE.md logs for `grep -B1` and friends.
checked=$(grep -c 'AXEYUM-ABC-CHECKED ' "$log" 2>/dev/null || true)
skipped=$(grep -c 'AXEYUM-ABC-SKIPPED' "$log" 2>/dev/null || true)
semantic=$(grep -c 'AXEYUM-ABC-SEMANTIC-CHECK ' "$log" 2>/dev/null || true)

echo "check-abc-crosscheck: $tests test(s), $semantic semantic (Aig::eval) check(s)," \
     "$checked real ABC &cec invocation(s), $skipped ABC-skip note(s)"

if [ "$semantic" = "0" ]; then
  echo "check-abc-crosscheck: ZERO semantic checks ran -- that half of the suite must never" \
       "be zero, ABC or no ABC." >&2
  exit 1
fi

if [ -n "$abc" ] && [ -n "$aigtoaig" ]; then
  # Both tools resolved: the ABC-backed half MUST have actually run.
  if [ "$checked" = "0" ]; then
    echo "check-abc-crosscheck: abc and aigtoaig both resolved, but ZERO real &cec" \
         "invocations were recorded. That is the defect this gate exists to catch." >&2
    exit 1
  fi
  if [ "$skipped" != "0" ]; then
    echo "check-abc-crosscheck: abc and aigtoaig both resolved, but the suite printed" \
         "AXEYUM-ABC-SKIPPED. A resolved binary must never be skipped." >&2
    grep 'AXEYUM-ABC-SKIPPED' "$log" >&2
    exit 1
  fi
  echo "check-abc-crosscheck: OK -- $checked curated pair(s)/negative control checked by" \
       "real abc at $abc (binary AIGER via $aigtoaig)."
else
  echo "check-abc-crosscheck: OK on the ABC-INDEPENDENT half only ($semantic semantic" \
       "check(s), including the negative control). The ABC-backed half did not run" \
       "(abc=${abc:-<absent>} aigtoaig=${aigtoaig:-<absent>}). Set AXEYUM_REQUIRE_ABC=1 on a" \
       "host that is supposed to have abc to turn this into a failure instead."
fi
