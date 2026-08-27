#!/usr/bin/env bash
# Controls for `scripts/check-deep-stack-call-sites.py`.
#
# The guard exists because a `#[test]` calling `build_creal_prelude` (or
# `build_complex_prelude`/`build_cpoint_prelude`/`build_creal_model_of_arith`)
# on a fresh kernel, without going through `on_a_deep_stack`, has SIGABRTed
# three separate debug test runs already (`creal_tests.rs`,
# `creal_model_tests.rs`, `prelude_cache_tests.rs`) and a fourth, real,
# previously-undetected instance (`the_derivative_is_stated_exactly`) was
# found by this very script before it had ever been wired into a gate.
#
# Every case here drives the checker against a SCRATCH directory (via
# `AXEYUM_DEEP_STACK_SEARCH_ROOT`), so no tracked file is mutated and no other
# lane's build is disturbed.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

CHECK="python3 scripts/check-deep-stack-call-sites.py"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

failures=0

# $1 case name, $2 expected exit, $3 a string the output must contain, $4 dir
run_case() {
  local name="$1" want="$2" needle="$3" dir="$4"
  local out status=0
  out=$(AXEYUM_DEEP_STACK_SEARCH_ROOT="$dir" $CHECK 2>&1) || status=$?
  if [ "$status" -ne "$want" ]; then
    echo "FAIL [$name]: expected exit $want, got $status" >&2
    printf '%s\n' "$out" | sed 's/^/    /' >&2
    failures=$(( failures + 1 ))
    return
  fi
  if [ "$(printf '%s' "$out" | /usr/bin/grep -c -- "$needle")" -eq 0 ]; then
    echo "FAIL [$name]: exit $status was right but the output never said '$needle'" >&2
    printf '%s\n' "$out" | sed 's/^/    /' >&2
    failures=$(( failures + 1 ))
    return
  fi
  echo "ok   [$name]"
}

write_fixture() {
  local dir="$1" name="$2" content="$3"
  mkdir -p "$dir"
  printf '%s' "$content" > "$dir/$name"
}

# --- 0. control: the real, currently-committed tree passes. If this fails,
#        a later red case is ambiguous between "the checker works" and
#        "something in the tree is already broken".
run_case "the committed tree passes" 0 "0 unprotected sites" \
  "crates/axeyum-lean-kernel/src"

# --- 1. a fresh, unwrapped call is RED and NAMES the test and the target.
write_fixture "$TMP/case1" "a.rs" '
#[test]
fn a_fresh_unprotected_build() {
    let mut kernel = Kernel::new();
    let p = build_creal_prelude(&mut kernel).expect("must build");
}
'
run_case "unwrapped direct call is RED" 1 "a_fresh_unprotected_build" "$TMP/case1"

# --- 2. the SAME call, reached one hop away through a same-file helper, is
#        still RED. This is the shape that actually shipped
#        (`the_derivative_is_stated_exactly` called `build_creal_prelude`
#        directly, no helper -- but `assert_reuse_matches_fresh_build` calling
#        `assert_reuse_matches_fresh_build_body` is the general shape this
#        case stands in for).
write_fixture "$TMP/case2" "b.rs" '
#[test]
fn reaches_through_a_helper() {
    helper();
}

fn helper() {
    let mut kernel = Kernel::new();
    let p = build_complex_prelude(&mut kernel).expect("must build");
}
'
run_case "unwrapped call one hop away is RED" 1 "reaches_through_a_helper" "$TMP/case2"

# --- 3. wrapping the closure inline is GREEN.
write_fixture "$TMP/case3" "c.rs" '
#[test]
fn wrapped_inline() {
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        let p = build_cpoint_prelude(&mut kernel).expect("must build");
    });
}
'
run_case "on_a_deep_stack closure is GREEN" 0 "0 unprotected sites" "$TMP/case3"

# --- 4. wrapping via a named `_body` function (the pattern this session used
#        for `creal/integral.rs` and `creal/sqrt.rs`) is GREEN.
write_fixture "$TMP/case4" "d.rs" '
#[test]
fn wrapped_via_body_fn() {
    on_a_deep_stack(wrapped_via_body_fn_body);
}

fn wrapped_via_body_fn_body() {
    let mut kernel = Kernel::new();
    let p = build_creal_model_of_arith(&mut kernel).expect("must build");
}
'
run_case "on_a_deep_stack(name) is GREEN" 0 "0 unprotected sites" "$TMP/case4"

# --- 5. an empty search root must not pass vacuously.
mkdir -p "$TMP/empty"
run_case "empty search root is exit 2, not a silent pass" 2 "refusing to pass vacuously" "$TMP/empty"

if [ "$failures" -gt 0 ]; then
  echo "$failures control(s) failed" >&2
  exit 1
fi
echo "all controls passed"
