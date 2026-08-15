#!/usr/bin/env bash
# Real-Lean gate: run every suite that hands generated modules to an EXTERNAL
# `lean` binary, and report HOW MANY Lean invocations actually happened.
#
# Why this exists, in one measurement. On 2026-08-14 all of these suites printed
# `ok` on a machine where Lean 4.30.0 was installed and had NEVER been pointed at
# our exported bytes. Every suite resolved its binary from `AXEYUM_LEAN_BIN` or
# `PATH` only; `elan` installs toolchains under `~/.elan/toolchains/*/bin/lean`
# and does not put them on `PATH`, so `which lean` printed nothing, a lane
# concluded "Lean is absent", and each suite took its skip path and passed. When
# a real Lean was finally run it REJECTED the modules (`a5975725f`:
# non-requested inductives were rendered as opaque `axiom`s, which have no iota
# rule, so any `Eq.refl` that had to compute through a recursor failed).
#
# So this gate does three things a bare `cargo test` cannot:
#
#   1. DISCOVERS the toolchain (`AXEYUM_LEAN_BIN`, then `PATH`, then
#      `$ELAN_HOME`/`~/.elan/toolchains/*/bin/lean`, then elan's shim) — the same
#      order as `crates/axeyum-lean-kernel/tests/support/lean_probe.rs`.
#   2. Sets `AXEYUM_REQUIRE_LEAN=1`, so a suite that cannot find the binary FAILS
#      instead of printing a skip note and passing.
#   3. COUNTS. Each suite prints `AXEYUM-LEAN-CHECKED <tag> checked=<n>`; this
#      script sums them and enforces a floor. An exit status cannot distinguish
#      "checked 40 modules" from "checked none", which is this repository's
#      signature defect (see `scripts/check-gate-liveness.sh` for the same trap
#      one level down, at the test-count layer).
#
# It also fails a suite that runs ZERO tests: `--features full` is mandatory on
# the `axeyum-solver` side and a missing flag compiles an empty binary that exits
# 0 (CLAUDE.md documents four suites this already happened to).
#
# Usage:
#   scripts/check-lean-gate.sh              # discover, require, count, enforce
#   AXEYUM_LEAN_BIN=/path/to/lean  …        # explicit override (authoritative)
#   AXEYUM_ALLOW_NO_LEAN=1         …        # no toolchain -> loud SKIP, exit 0
#
# NO TOOLCHAIN IS A FAILURE BY DEFAULT. That is deliberate: the whole incident
# above is what "absent Lean quietly passes" looks like. A machine that genuinely
# has no Lean sets `AXEYUM_ALLOW_NO_LEAN=1` and gets a banner saying, in words,
# that zero Lean checks ran.
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2

# The floor. Measured 2026-08-14 on Lean 4.30.0: 112 real-Lean invocations across
# the twelve suites below (kernel side 21, solver side 91 — of which 70 are
# `lean_crosscheck`'s one-module-per-family representative slice). Set with
# headroom so ordinary churn does not trip it; RAISING it as suites grow is the
# ratchet working, LOWERING it needs a reason in the commit message.
#
# Raised 105 -> 107 on 2026-08-15 by lane `import-scale`:
# `real_lean_nat_arithmetic_crosscheck` adds two invocations, handing official
# Lean 24 literal-arithmetic answers THIS kernel computed (plus a negative
# control). Thirteen suites now; measured total 115.
#
# Raised 107 -> 109 on 2026-08-15 by lane `import-strings`:
# `real_lean_string_literal_crosscheck` adds two more, handing official Lean ten
# Unicode-scalar expansions read back out of THIS kernel's reducts (plus a
# negative control covering both a byte-oriented decode and a reordered list).
# Fourteen suites now; measured total 117.
CHECK_FLOOR="${AXEYUM_LEAN_CHECK_FLOOR:-109}"

# package | features | test target
#
# `lean_crosscheck` (axeyum-solver, `full`) is the 70-family representative
# sweep, and it is LISTED. Running it under real Lean for the first time on
# 2026-08-14 found a genuine rejection — the `quant_bv_source_instance_set`
# family — which was excluded here by name until it was fixed. It was a WRITER
# defect, not a reconstruction defect: the compact proof-sharing pass hoisted a
# *proper prefix* of a recursor spine (`def axeyum_proof_share_149 := @Or.rec P`),
# and Lean makes an inductive's parameters and a recursor's motive implicit, so
# the bare reference `axeyum_proof_share_149 Q` silently re-inserted them and put
# `Q` in the wrong slot. The kernel term was well typed throughout; only the
# module text was wrong. Fixed by keeping regenerated-constant spines saturated
# (`lean_pp::hoisting_exposes_implicit_binders`), with the dedicated regression
# suite `real_lean_compact_share_crosscheck` below. 70 of 70 families now pass;
# the exhaustive `-- --ignored` run checks 163 of 163 modules.
suites=$(
  cat <<'EOF'
axeyum-lean-kernel||real_lean_inductive_crosscheck
axeyum-lean-kernel||real_lean_parametric_inductive_crosscheck
axeyum-lean-kernel||real_lean_strict_positivity_crosscheck
axeyum-lean-kernel||real_lean_nat_literal_crosscheck
axeyum-lean-kernel||real_lean_nat_arithmetic_crosscheck
axeyum-lean-kernel||real_lean_string_literal_crosscheck
axeyum-lean-kernel||real_lean_structure_eta_crosscheck
axeyum-lean-kernel||real_lean_compact_share_crosscheck
axeyum-lean-kernel||real_lean_kernel_replay
axeyum-solver|full|int_inequality_lean_reconstruct
axeyum-solver|full|lean_module_fixtures
axeyum-solver|full|diophantine_lean_reconstruct
axeyum-solver|full|regex_emptiness_lean_reconstruct
axeyum-solver|full|lean_crosscheck
EOF
)

# ---------------------------------------------------------------------------
# Discovery. Mirrors `lean_probe::lean_bin`, including the rule that an explicit
# `AXEYUM_LEAN_BIN` is authoritative in BOTH directions: if it is set and does
# not resolve we do NOT search on, or `AXEYUM_LEAN_BIN=/nonexistent` (the
# negative control for this gate) would quietly find the elan toolchain instead.
# ---------------------------------------------------------------------------
discover_lean() {
  if [ -n "${AXEYUM_LEAN_BIN:-}" ]; then
    [ -x "$AXEYUM_LEAN_BIN" ] && printf '%s\n' "$AXEYUM_LEAN_BIN"
    return
  fi
  local candidate
  if candidate=$(command -v lean 2>/dev/null); then
    printf '%s\n' "$candidate"
    return
  fi
  local root="${ELAN_HOME:-${HOME:-}/.elan}"
  [ -d "$root/toolchains" ] || { [ -x "$root/bin/lean" ] && printf '%s\n' "$root/bin/lean"; return; }
  # Deterministic order: sort toolchain directory names, newest name first.
  local toolchain
  while IFS= read -r toolchain; do
    [ -x "$toolchain/bin/lean" ] && { printf '%s\n' "$toolchain/bin/lean"; return; }
  done < <(find "$root/toolchains" -mindepth 1 -maxdepth 1 -type d | LC_ALL=C sort -r)
  [ -x "$root/bin/lean" ] && printf '%s\n' "$root/bin/lean"
}

lean=$(discover_lean)
if [ -z "$lean" ]; then
  echo "check-lean-gate: searched AXEYUM_LEAN_BIN='${AXEYUM_LEAN_BIN:-<unset>}', PATH," \
       "and ${ELAN_HOME:-${HOME:-}/.elan}/toolchains/*/bin/lean -- no Lean binary." >&2
  if [ "${AXEYUM_ALLOW_NO_LEAN:-}" = "1" ]; then
    echo "check-lean-gate: SKIPPED -- 0 real-Lean checks ran. This is NOT a pass;" \
         "AXEYUM_ALLOW_NO_LEAN=1 was set, so nothing external read our exported modules." >&2
    exit 0
  fi
  echo "check-lean-gate: FAILED. Install a toolchain (\`elan toolchain install leanprover/lean4:v4.30.0\`)," \
       "point AXEYUM_LEAN_BIN at a \`lean\`, or set AXEYUM_ALLOW_NO_LEAN=1 to accept a run in which" \
       "ZERO Lean checks happen." >&2
  exit 1
fi

version=$("$lean" --version 2>&1 | head -1)
echo "check-lean-gate: using $lean"
echo "check-lean-gate: $version"

export AXEYUM_LEAN_BIN="$lean"
export AXEYUM_REQUIRE_LEAN=1

scratch=$(mktemp -d) || exit 2
trap 'rm -rf "$scratch"' EXIT

fail=0
failed_suites=()
total_checked=0
total_tests=0
suite_count=0

while IFS='|' read -r package features target; do
  [ -n "$target" ] || continue
  suite_count=$((suite_count + 1))
  log="$scratch/$target.log"
  args=(test -q -p "$package")
  [ -n "$features" ] && args+=(--features "$features")
  args+=(--test "$target" -- --nocapture)
  if ! cargo "${args[@]}" >"$log" 2>&1; then
    echo "check-lean-gate: SUITE FAILED: $package/$target" >&2
    tail -40 "$log" >&2
    failed_suites+=("$target")
    fail=1
  fi

  ran=$(grep -c '^running [0-9]* test' "$log" 2>/dev/null || true)
  tests=$(sed -n 's/^running \([0-9]*\) test.*/\1/p' "$log" | awk '{s+=$1} END {print s+0}')
  checked=$(sed -n 's/.*AXEYUM-LEAN-CHECKED [^ ]* checked=\([0-9]*\).*/\1/p' "$log" |
    awk '{s+=$1} END {print s+0}')
  skipped=$(grep -c 'AXEYUM-LEAN-SKIPPED' "$log" 2>/dev/null || true)

  total_tests=$((total_tests + tests))
  total_checked=$((total_checked + checked))

  if [ "$ran" = "0" ] || [ "$tests" = "0" ]; then
    echo "check-lean-gate: $target compiled to ZERO tests -- the 'running 0 tests ... ok' trap." \
         "Check the feature flags for this target." >&2
    failed_suites+=("$target(0-tests)")
    fail=1
  fi
  if [ "$skipped" != "0" ]; then
    echo "check-lean-gate: $target printed AXEYUM-LEAN-SKIPPED under AXEYUM_REQUIRE_LEAN=1;" \
         "a skip must never reach this gate." >&2
    grep 'AXEYUM-LEAN-SKIPPED' "$log" >&2
    failed_suites+=("$target(skipped)")
    fail=1
  fi
  if [ "$checked" = "0" ]; then
    echo "check-lean-gate: $target ran $tests test(s) but reported ZERO real-Lean checks." >&2
    failed_suites+=("$target(0-lean-checks)")
    fail=1
  fi
  printf 'check-lean-gate: %-45s %3s test(s), %3s real-Lean check(s)\n' "$target" "$tests" "$checked"
done <<<"$suites"

echo "check-lean-gate: $suite_count suites, $total_tests tests, $total_checked real-Lean checks" \
     "(floor $CHECK_FLOOR)"

if [ "$total_checked" -lt "$CHECK_FLOOR" ]; then
  echo "check-lean-gate: only $total_checked real-Lean checks ran, below the committed floor of" \
       "$CHECK_FLOOR -- checks have been lost. If that was deliberate, lower CHECK_FLOOR in this" \
       "file and say why." >&2
  fail=1
fi

if [ "$fail" -ne 0 ]; then
  [ ${#failed_suites[@]} -gt 0 ] && printf 'check-lean-gate: FAILED: %s\n' "${failed_suites[*]}" >&2
  exit 1
fi
echo "check-lean-gate: OK -- $total_checked modules/controls were read by a real Lean kernel"
