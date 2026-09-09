#!/usr/bin/env bash
# Real-Carcara gate: run the suite that hands our emitted Alethe proofs to an
# EXTERNAL `carcara` binary, and report HOW MANY Carcara invocations actually
# happened.
#
# Why this exists, in two measurements.
#
# 1. `crates/axeyum-solver/tests/carcara_crosscheck.rs` resolves its binary from
#    `AXEYUM_CARCARA_BIN` or the gitignored `references/carcara/target/release/`
#    build, and every one of its ~83 tests returns early with a `[skip]` note --
#    and PASSES -- when that binary is absent. No gate in this repository ever
#    ran Carcara, so nothing has ever failed here for the reason the suite
#    exists. The suite's own header says it: "A skipping suite is a suite that
#    has never been shown to fail."
#
# 2. Carcara's exit status cannot distinguish a fully-checked proof from one
#    full of holes. `cli/src/main.rs:35-45`: `check()` returns
#    `Result<bool, Error>` where the bool is `is_holey`; the CLI prints "valid"
#    for `Ok(false)`, "holey" for `Ok(true)`, and RETURNS NORMALLY (exit 0) in
#    both cases -- only `Err` reaches `std::process::exit(1)`. Measured against
#    carcara 1.1.0 (git 6624ea8) on 2026-09-09 with a three-line Alethe proof:
#
#      :rule resolution           -> "valid"    exit 0
#      :rule hole                 -> "holey"    exit 0     <-- the trap
#      :rule read_over_write_same -> "invalid"  exit 1     (unknown rule)
#
#    So the verdict is the STDOUT LINE, never `$?`. This is cvc5's discipline
#    too (`references/cvc5/test/regress/cli/run_regression.py:312-335`: check
#    the exit status AND then separately `if "valid" not in output`), except we
#    parse the line exactly rather than by substring -- "invalid" contains
#    "valid", and a substring test therefore accepts Carcara's own rejection.
#
# So this gate does four things a bare `cargo test` cannot:
#
#   1. RESOLVES the binary and prints its version, so a result names its checker.
#   2. Sets `AXEYUM_REQUIRE_CARCARA=1`, so a suite that cannot find the binary
#      FAILS instead of printing a skip note and passing. NO BINARY IS A FAILURE
#      BY DEFAULT -- that is the whole point. A machine that genuinely has no
#      Carcara sets `AXEYUM_ALLOW_NO_CARCARA=1` and gets a banner saying, in
#      words, that zero Carcara checks ran.
#   3. COUNTS. Each invocation prints `AXEYUM-CARCARA-CHECKED <tag> verdict=<v>`;
#      this script sums them and enforces a floor. An exit status cannot
#      distinguish "checked 90 proofs" from "checked none", which is this
#      repository's signature defect (`scripts/check-gate-liveness.sh` is the
#      same trap one level down).
#   4. FAILS a suite that runs ZERO tests: `--features full` is mandatory on this
#      target (`#![cfg(feature = "full")]` at the top of the suite) and a missing
#      flag compiles an empty binary that prints "running 0 tests ... ok".
#
# Usage:
#   scripts/check-carcara-gate.sh              # resolve, require, count, enforce
#   scripts/check-carcara-gate.sh --self-check # the gate's own negative control
#   scripts/check-carcara-gate.sh --print-bin  # resolve and print, run nothing
#
# `--self-check` needs no cargo build: it writes four three-line Alethe proofs
# over one two-clause problem and asserts this script classifies each the way
# the table above measured. It is the answer to "delete one guard and require
# that exactly one test dies" -- flip `verdict_of`'s `holey` arm to accept and
# `--self-check` fails on the `hole` case alone.
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2

# The floor on real Carcara invocations. Set to 1 initially and RAISED once the
# suite has been run against a binary on a gate host: raising it as the suite
# grows is the ratchet working, LOWERING it needs a reason in the commit message.
# A floor of 1 already closes the defect this gate exists for (every previous run
# made ZERO invocations); a higher floor additionally catches silent skips.
CHECK_FLOOR="${AXEYUM_CARCARA_CHECK_FLOOR:-40}"

# The suite. One target today; the loop is written for more.
SUITES="axeyum-solver|full|carcara_crosscheck"

# ---------------------------------------------------------------------------
# The three rules our Alethe emitters name that Carcara has no checker for.
# ---------------------------------------------------------------------------
#
# `read_over_write` and `read_over_write_same` are our array rules (Carcara
# spells the checked ones `arrays_idx`/`arrays_row`); `bv_poly_simp` is the
# Route-2 bvsub rewrite. Sources: `docs/solver-inventory-2026-09/08-models-
# proofs-and-evidence.md:285-291`, `docs/solver-comparison-2026-09/03-cvc5.md:966`,
# and the pinned assertions in `crates/axeyum-cnf/src/alethe.rs`
# (`the_axeyum_internal_array_rules_are_not_carcara_rules`).
#
# They are passed to Carcara EXPLICITLY, as cvc5 does for its own three
# (`--allowed-rules undefined la_mult_sign la_mult_abs_comparison`). Naming them
# turns them from "invalid, unknown rule" into declared HOLES, which this gate
# still rejects -- but an UNEXPECTED unknown rule now reads as `invalid` and is
# distinguishable from a known gap. Silently tolerating them (by not running
# Carcara at all, which is what happened before this gate) makes the two
# indistinguishable.
#
# ARGUMENT ORDER IS LOAD-BEARING. `--allowed-rules` is declared `multiple = true`
# (`references/carcara/cli/src/app.rs:175-177`), so it greedily eats following
# positionals. Measured 2026-09-09:
#   carcara check --allowed-rules a --allowed-rules b PROOF PROBLEM
#     -> "error: The following required arguments were not provided: <PROOF_FILE>"
#   carcara check PROOF PROBLEM --allowed-rules a b c      -> works
#   carcara check --allowed-rules a b c -- PROOF PROBLEM   -> works
# We use the first working form: positionals, then the flag last.
ALLOWED_RULES=(read_over_write read_over_write_same bv_poly_simp)

# ---------------------------------------------------------------------------
# Binary resolution
# ---------------------------------------------------------------------------
resolve_carcara() {
  if [ -n "${AXEYUM_CARCARA_BIN:-}" ]; then
    if [ -x "$AXEYUM_CARCARA_BIN" ]; then
      printf '%s\n' "$AXEYUM_CARCARA_BIN"
      return 0
    fi
    echo "check-carcara-gate: AXEYUM_CARCARA_BIN=$AXEYUM_CARCARA_BIN is not executable." >&2
    return 1
  fi
  local vendored="references/carcara/target/release/carcara"
  if [ -x "$vendored" ]; then
    printf '%s\n' "$vendored"
    return 0
  fi
  return 1
}

carcara=$(resolve_carcara)
if [ -z "$carcara" ]; then
  if [ "${AXEYUM_ALLOW_NO_CARCARA:-}" = "1" ]; then
    echo "check-carcara-gate: AXEYUM_ALLOW_NO_CARCARA=1 -- ZERO Carcara checks ran." \
         "Nothing in this run establishes that a third party accepts our Alethe proofs." >&2
    exit 0
  fi
  cat >&2 <<'NOBIN'
check-carcara-gate: FAILED -- no `carcara` binary.

This is a FAILURE and not a skip on purpose. Every test in
`crates/axeyum-solver/tests/carcara_crosscheck.rs` returns early and PASSES when
the binary is absent, so an absent Carcara used to look exactly like a Carcara
that accepted every proof we emit.

To fix, either build it:

    scripts/fetch-references.sh          # or a shallow clone into references/
    cd references/carcara
    RUSTUP_TOOLCHAIN=stable cargo build --release -p carcara-cli

(its `rust-toolchain.toml` pins 1.87, which may not be installable; `rug`'s
`gmp-mpfr-sys` build needs `m4` on PATH)

...or point at one:   AXEYUM_CARCARA_BIN=/path/to/carcara

...or state, deliberately, that this host has none and that therefore no
external Alethe check ran:   AXEYUM_ALLOW_NO_CARCARA=1
NOBIN
  exit 1
fi

carcara_version=$("$carcara" --version 2>&1 | head -1)
carcara_real=$(readlink -f "$carcara" 2>/dev/null || printf '%s' "$carcara")

if [ "${1:-}" = "--print-bin" ]; then
  printf '%s\t%s\t%s\n' "$carcara" "$carcara_real" "$carcara_version"
  exit 0
fi

# ---------------------------------------------------------------------------
# The verdict parser -- the thing this whole gate turns on.
# ---------------------------------------------------------------------------
#
# Carcara's `check` subcommand prints exactly one of `valid`, `holey`, `invalid`
# on its own line (`cli/src/main.rs:35-45`). Anything else -- a crash, a clap
# usage error, a timeout kill -- is `unparsed`, which is a FAILURE and not a
# pass: a gate that cannot read a verdict has not read one.
#
# Matched as WHOLE LINES. `invalid` contains `valid` as a substring, so the
# obvious `grep valid` (and cvc5's own `"valid" not in output`) accepts
# Carcara's rejection as an acceptance.
verdict_of() {
  local out_file="$1" v=""
  local line
  while IFS= read -r line; do
    case "$(printf '%s' "$line" | tr -d '\r' | sed 's/^[[:space:]]*//; s/[[:space:]]*$//')" in
      valid) v=valid ;;
      holey) v=holey ;;
      invalid) v=invalid ;;
    esac
  done <"$out_file"
  printf '%s' "${v:-unparsed}"
}

# Runs Carcara on one (proof, problem) pair; echoes the verdict. Never returns
# the process's exit status as the answer.
run_carcara() {
  local proof="$1" problem="$2" out="$3"
  "$carcara" check "$proof" "$problem" --allowed-rules "${ALLOWED_RULES[@]}" \
    >"$out" 2>&1
  verdict_of "$out"
}

# The gate's acceptance rule, in one place: ONLY `valid` is a pass.
#
# `holey` is not. A hole is a step Carcara declined to check -- either its own
# `hole`/`lia_generic`/`rare_rewrite`, or one of the rules we declared above --
# and an artifact whose steps are holes is not an externally-checked artifact.
# This mirrors `axeyum_solver::Evidence::portable_artifact` and the Rust suite's
# `CarcaraVerdict::Valid`-only assertion; the two must agree.
gate_accepts() {
  [ "$1" = "valid" ]
}

# ---------------------------------------------------------------------------
# --self-check: the gate's own negative control, no cargo build required.
# ---------------------------------------------------------------------------
if [ "${1:-}" = "--self-check" ]; then
  scratch=$(mktemp -d) || exit 2
  trap 'rm -rf "$scratch"' EXIT

  cat >"$scratch/problem.smt2" <<'SMT'
(set-logic QF_UF)
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
SMT

  # One proof shape, one rule name changed per case. Only the rule differs, so a
  # verdict difference is attributable to the rule and to nothing else.
  #   resolution            -- a rule Carcara checks             -> valid
  #   hole                  -- Carcara's own unconditional hole  -> holey  (EXIT 0)
  #   read_over_write_same  -- one of OUR three, declared above  -> holey  (EXIT 0)
  #   totally_bogus_rule    -- an unexpected unknown rule        -> invalid
  self_fail=0
  # rule | expected verdict | expected gate decision
  for case in "resolution valid pass" "hole holey fail" \
              "read_over_write_same holey fail" "totally_bogus_rule invalid fail"; do
    set -- $case
    rule=$1
    want=$2
    want_gate=$3
    printf '(assume a0 p)\n(assume a1 (not p))\n(step t1 (cl) :rule %s :premises (a0 a1))\n' \
      "$rule" >"$scratch/proof.alethe"
    "$carcara" check "$scratch/proof.alethe" "$scratch/problem.smt2" \
      --allowed-rules "${ALLOWED_RULES[@]}" >"$scratch/out" 2>&1
    status=$?
    got=$(verdict_of "$scratch/out")
    if gate_accepts "$got"; then got_gate=pass; else got_gate=fail; fi
    if [ "$got" != "$want" ] || [ "$got_gate" != "$want_gate" ]; then
      echo "check-carcara-gate --self-check: rule '$rule' gave verdict '$got' ($got_gate)," \
           "expected '$want' ($want_gate) (carcara exit $status). Output:" >&2
      cat "$scratch/out" >&2
      self_fail=1
    else
      printf 'check-carcara-gate --self-check: :rule %-22s -> %-8s gate=%-4s (carcara exit %s)\n' \
        "$rule" "$got" "$got_gate" "$status"
    fi
    # The load-bearing half: `hole` and one of our own rules BOTH exit 0. If a
    # gate trusted `$?` it would pass them.
    if [ "$want" = "holey" ] && [ "$status" -ne 0 ]; then
      echo "check-carcara-gate --self-check: expected carcara to EXIT 0 on '$rule' (that is" \
           "why the exit status is not the verdict); it exited $status. Re-read" \
           "cli/src/main.rs before trusting this gate's comments." >&2
      self_fail=1
    fi
  done

  if [ "$self_fail" -ne 0 ]; then
    echo "check-carcara-gate --self-check: FAILED" >&2
    exit 1
  fi
  echo "check-carcara-gate --self-check: OK -- $carcara_version at $carcara." \
       "A proof whose only change is one rule renamed to \`hole\` is REJECTED (holey)" \
       "even though Carcara exits 0."
  exit 0
fi

# ---------------------------------------------------------------------------
# The gate proper: run the suite with the binary REQUIRED, and count.
# ---------------------------------------------------------------------------
export AXEYUM_CARCARA_BIN="$carcara"
export AXEYUM_REQUIRE_CARCARA=1

echo "check-carcara-gate: using $carcara_version ($carcara)"

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
    echo "check-carcara-gate: SUITE FAILED: $package/$target" >&2
    tail -60 "$log" >&2
    failed_suites+=("$target")
    fail=1
  fi

  ran=$(grep -c '^running [0-9]* test' "$log" 2>/dev/null || true)
  tests=$(sed -n 's/^running \([0-9]*\) test.*/\1/p' "$log" | awk '{s+=$1} END {print s+0}')
  checked=$(grep -c 'AXEYUM-CARCARA-CHECKED ' "$log" 2>/dev/null || true)
  skipped=$(grep -c 'AXEYUM-CARCARA-SKIPPED' "$log" 2>/dev/null || true)
  # WHICH binary did the suite actually use? Exporting AXEYUM_CARCARA_BIN is an
  # instruction, not evidence. The suite prints one banner naming what it
  # resolved; a count over a different checker is not this gate's count.
  used_bins=$(sed -n 's/.*AXEYUM-CARCARA-BIN bin=\(.*\) version=.*/\1/p' "$log" |
    LC_ALL=C sort -u)

  total_tests=$((total_tests + tests))
  total_checked=$((total_checked + checked))

  if [ "$ran" = "0" ] || [ "$tests" = "0" ]; then
    echo "check-carcara-gate: $target compiled to ZERO tests -- the 'running 0 tests ... ok'" \
         "trap. This target is #![cfg(feature = \"full\")]; check the feature flags." >&2
    failed_suites+=("$target(0-tests)")
    fail=1
  fi
  if [ "$skipped" != "0" ]; then
    echo "check-carcara-gate: $target printed AXEYUM-CARCARA-SKIPPED under" \
         "AXEYUM_REQUIRE_CARCARA=1; a skip must never reach this gate." >&2
    grep 'AXEYUM-CARCARA-SKIPPED' "$log" >&2
    failed_suites+=("$target(skipped)")
    fail=1
  fi
  if [ "$checked" = "0" ]; then
    echo "check-carcara-gate: $target ran $tests test(s) but reported ZERO Carcara" \
         "invocations. That is the defect this gate exists to catch." >&2
    failed_suites+=("$target(0-carcara-checks)")
    fail=1
  fi
  if [ -z "$used_bins" ] && [ "$checked" != "0" ]; then
    echo "check-carcara-gate: $target reported $checked Carcara check(s) but printed no" \
         "AXEYUM-CARCARA-BIN banner, so which checker produced them is unknown. A result" \
         "that does not name its checker is not evidence." >&2
    failed_suites+=("$target(unnamed-checker)")
    fail=1
  elif [ -n "$used_bins" ]; then
    while IFS= read -r used; do
      [ -n "$used" ] || continue
      used_real=$(readlink -f "$used" 2>/dev/null || printf '%s' "$used")
      if [ "$used_real" != "$carcara_real" ]; then
        echo "check-carcara-gate: $target used $used, not the resolved $carcara." >&2
        failed_suites+=("$target(wrong-binary)")
        fail=1
      fi
    done <<<"$used_bins"
  fi
  printf 'check-carcara-gate: %-30s %4s test(s), %4s Carcara invocation(s)\n' \
    "$target" "$tests" "$checked"
done <<<"$SUITES"

echo "check-carcara-gate: $suite_count suite(s), $total_tests tests," \
     "$total_checked Carcara invocation(s) (floor $CHECK_FLOOR)"

if [ "$total_checked" -lt "$CHECK_FLOOR" ]; then
  echo "check-carcara-gate: only $total_checked Carcara invocation(s) ran, below the committed" \
       "floor of $CHECK_FLOOR -- checks have been lost. If that was deliberate, lower" \
       "CHECK_FLOOR in this file and say why." >&2
  fail=1
fi

if [ "$fail" -ne 0 ]; then
  [ ${#failed_suites[@]} -gt 0 ] && printf 'check-carcara-gate: FAILED: %s\n' "${failed_suites[*]}" >&2
  exit 1
fi
echo "check-carcara-gate: OK -- $total_checked of our Alethe proofs were READ by" \
     "$carcara_version ($carcara), with ${ALLOWED_RULES[*]} declared as known holes."
