#!/usr/bin/env bash
# Controls for `scripts/check-lean-golden-pins.sh`: run the REAL script against
# synthetic trees, one scenario at a time, and assert both the exit status and
# that the message names the right thing.
#
# Per CLAUDE.md: a checker that cannot fail is worse than no checker. Every
# scenario below is one the gate must REJECT, plus exactly one it must ACCEPT.
# `AXEYUM_GOLDEN_PIN_ROOT` and `AXEYUM_CARGO` are the hooks that make this
# possible -- the same shipped script, a throwaway tree, and a stub cargo whose
# transcript is whatever the scenario needs.
#
# Each control is tied to ONE guard. Deleting a guard in the script must kill
# EXACTLY ONE of these; if it kills several, the guards share a check and the
# suite is weaker than its count suggests (six of seven guards in one suite here
# were once removable with everything still green, for exactly that reason).
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2

SCRIPT="$PWD/scripts/check-lean-golden-pins.sh"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
fail=0

# A stub `cargo` that prints a cargo-shaped transcript. $1 is the per-suite test
# count to claim; the suite names come from the `--test` flags it is passed.
make_cargo() {
  local path="$1" count="$2"
  cat >"$path" <<STUB
#!/usr/bin/env bash
for arg in "\$@"; do
  if [ "\$prev" = "--test" ]; then
    echo "     Running tests/\$arg.rs (/t/debug/deps/\$arg-0)"
    echo "running $count tests"
    echo "test result: ok. $count passed; 0 failed"
  fi
  prev="\$arg"
done
exit 0
STUB
  chmod +x "$path"
}

# A tree with one golden suite that uses the helper, plus the banner-pin suite
# the gate always adds.
make_tree() {
  local root="$1" body="$2"
  rm -rf "$root"
  mkdir -p "$root/crates/axeyum-solver/tests" "$root/crates/axeyum-lean-kernel/tests" "$root/scripts"
  printf '%s\n' "$body" >"$root/crates/axeyum-solver/tests/a_golden.rs"
  : >"$root/crates/axeyum-lean-kernel/tests/module_banner_pin.rs"
}

HELPER_SUITE='#![cfg(feature = "full")]
fn t() { let s = reconstruct_to_lean_module(); lean_golden::assert_golden_module("a", &s, (1, 2)); }'
HANDROLLED_SUITE='#![cfg(feature = "full")]
fn t() {
    let s = reconstruct_to_lean_module();
    let h = s.bytes().fold(0xcbf2_9ce4_8422_2325_u64, |h, b| h);
    assert_eq!((s.len(), h), (1, 2));
}'

check() { # name expected_rc must_match logfile
  local name="$1" want="$2" pattern="$3" log="$4" got="$5"
  if [ "$got" != "$want" ]; then
    echo "FAIL: $name — exit $got, expected $want"; sed -n 1,20p "$log"; fail=1; return
  fi
  if [ -n "$pattern" ] && ! grep -q "$pattern" "$log"; then
    echo "FAIL: $name — exit $got as expected but the message never says '$pattern'"
    sed -n 1,20p "$log"; fail=1; return
  fi
  echo "ok: $name"
}

make_cargo "$WORK/cargo-ok" 3
make_cargo "$WORK/cargo-empty" 0

# 1. ACCEPT: a helper-using golden suite, cargo reports tests.
make_tree "$WORK/t1" "$HELPER_SUITE"
AXEYUM_GOLDEN_PIN_ROOT="$WORK/t1" AXEYUM_CARGO="$WORK/cargo-ok" "$SCRIPT" >"$WORK/l1" 2>&1
check "a helper-using golden suite is accepted" 0 "2 golden-module suites green" "$WORK/l1" "$?"

# 2. REJECT: a hand-rolled whole-module pin that dodges the helper. This is the
#    exact shape that put the banner back under the pins three times.
# The tree also carries a compliant suite, so the discovery FLOOR does not fire
# here: each control must isolate one guard (the first draft of this one failed
# for that reason -- two guards, one scenario, and deleting either looked the
# same).
make_tree "$WORK/t2" "$HELPER_SUITE"
printf '%s\n' "$HANDROLLED_SUITE" >"$WORK/t2/crates/axeyum-solver/tests/b_handrolled.rs"
AXEYUM_GOLDEN_PIN_ROOT="$WORK/t2" AXEYUM_CARGO="$WORK/cargo-ok" "$SCRIPT" >"$WORK/l2" 2>&1
check "a hand-rolled whole-module pin is refused" 1 "does not use" "$WORK/l2" "$?"

# 3. REJECT: nothing discovered. A gate that finds no golden suites has either
#    lost them all or lost the string it searches for; it must not print ok.
make_tree "$WORK/t3" 'fn t() {}'
AXEYUM_GOLDEN_PIN_ROOT="$WORK/t3" AXEYUM_CARGO="$WORK/cargo-ok" "$SCRIPT" >"$WORK/l3" 2>&1
check "a tree with no golden pins is refused" 1 "discovered" "$WORK/l3" "$?"

# 4. REJECT: the suite compiled but ran ZERO tests (`cargo test` exits 0 on an
#    empty binary — the failure mode that hid an inert corpus gate for 15 days).
make_tree "$WORK/t4" "$HELPER_SUITE"
AXEYUM_GOLDEN_PIN_ROOT="$WORK/t4" AXEYUM_CARGO="$WORK/cargo-empty" "$SCRIPT" >"$WORK/l4" 2>&1
check "a suite that runs zero tests is refused" 1 "ZERO tests" "$WORK/l4" "$?"

# 5. REJECT: a failing cargo run. Obvious, and it is the control that dies if the
#    status of the group stops being read at all.
make_tree "$WORK/t5" "$HELPER_SUITE"
printf '#!/usr/bin/env bash\n%s\nexit 101\n' \
  'for a in "$@"; do if [ "$p" = "--test" ]; then echo "     Running tests/$a.rs (/t/x)"; echo "running 3 tests"; fi; p="$a"; done' \
  >"$WORK/cargo-fail"; chmod +x "$WORK/cargo-fail"
AXEYUM_GOLDEN_PIN_ROOT="$WORK/t5" AXEYUM_CARGO="$WORK/cargo-fail" "$SCRIPT" >"$WORK/l5" 2>&1
check "a failing suite is refused" 1 "group FAILED" "$WORK/l5" "$?"

# 6. The real repository must pass its own discovery: --list is cheap and must
#    find the five golden suites plus the banner pin.
"$SCRIPT" --list >"$WORK/l6" 2>&1
rc=$?
if [ "$rc" -ne 0 ] || [ "$(grep -c 'listed' "$WORK/l6")" -lt 6 ]; then
  echo "FAIL: this repository discovers fewer than 6 golden-module suites"
  cat "$WORK/l6"; fail=1
else
  echo "ok: this repository discovers $(grep -c 'listed' "$WORK/l6") golden-module suites"
fi

[ "$fail" -eq 0 ] && echo "check-lean-golden-pins controls: all green"
exit "$fail"
