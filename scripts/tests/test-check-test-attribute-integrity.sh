#!/usr/bin/env bash
# Controls for scripts/check-test-attribute-integrity.py.
#
# Each case names the incident it pins. The gate exists because a `splice`
# merge put an item BETWEEN a `#[test]` and its function on 2026-08-29 and one
# test silently never ran while `cargo test` reported a healthy count.
#
# Every guard here is mutation-verified to be killed by EXACTLY ONE case; run
# with --mutants to re-check that.
set -u
GATE="$(cd "$(dirname "$0")/.." && pwd)/check-test-attribute-integrity.py"
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
pass=0; fail=0

run_case() {  # name expected_exit dir
  local name="$1" want="$2" dir="$3"
  python3 "$GATE" "$dir" > "$TMP/out" 2>&1
  local got=$?
  if [ "$got" = "$want" ]; then
    printf 'ok    %s\n' "$name"; pass=$((pass+1))
  else
    printf 'FAIL  %s (want exit %s, got %s)\n' "$name" "$want" "$got"
    sed 's/^/        /' "$TMP/out"; fail=$((fail+1))
  fi
}

# --- the real incident: an item spliced between `#[test]` and its function ---
mkdir -p "$TMP/spliced"
cat > "$TMP/spliced/a.rs" <<'RS'
#[test]
/// A doc comment for a DIFFERENT item that got spliced in here.
fn victim() { assert!(true); }
RS
# ^ this one is actually well-formed; the damaged shape is below
cat > "$TMP/spliced/b.rs" <<'RS'
#[test]
const NOT_A_FUNCTION: u32 = 1;

fn orphaned_from_its_attribute() { assert!(true); }
RS
run_case "an item between #[test] and its fn is caught" 1 "$TMP/spliced"

# --- the duplicated-attribute half of the same incident ---
mkdir -p "$TMP/dup"
cat > "$TMP/dup/a.rs" <<'RS'
#[test]
#[test]
fn doubly_attributed() { assert!(true); }
RS
run_case "a duplicated #[test] is caught" 1 "$TMP/dup"

# --- FALSE-POSITIVE control: a multi-line attribute is NOT damage ---
# The first draft of this gate flagged three healthy files this way, because it
# matched an attribute's opening line and stopped inside it.
mkdir -p "$TMP/multiline"
cat > "$TMP/multiline/a.rs" <<'RS'
#[test]
#[allow(
    clippy::many_single_char_names,
    clippy::too_many_lines
)]
fn healthy_with_a_wrapped_attribute() { assert!(true); }
RS
run_case "a multi-line #[allow] between #[test] and fn is NOT flagged" 0 "$TMP/multiline"

# --- other legal shapes must stay green ---
mkdir -p "$TMP/legal"
cat > "$TMP/legal/a.rs" <<'RS'
#[test]
#[should_panic]
fn panics() { panic!("x"); }

#[tokio::test]
async fn async_test() { assert!(true); }

#[test]
// an ordinary comment
/// and a doc comment
pub fn public_test() { assert!(true); }
RS
run_case "should_panic / async / pub / comments stay green" 0 "$TMP/legal"

# --- scanned-nothing must NOT read as a pass ---
mkdir -p "$TMP/empty"
run_case "a root with no .rs files exits 2, not 0" 2 "$TMP/empty"

printf '\ncheck-test-attribute-integrity controls: %d passed, %d failed\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
