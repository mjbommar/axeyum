#!/usr/bin/env bash
# Controls for scripts/recount-pinned-inventory.py.
#
# The guard that matters is the WRAPPED-entry branch. rustfmt splits any
# inventory entry whose name is long across five lines, beginning with a bare
# `(` on its own line, so a counter that only recognizes the single-line form
# undercounts -- measured 2026-08-26 at 210 against a true 283, and the wrong
# number was written into `creal_tests.rs` before the discrepancy surfaced.
#
# Each case below is mutation-verified to die on exactly one guard:
#   * drop the WRAPPED regex  -> `wrapped_entries_are_counted` fails
#   * drop the SINGLE regex   -> `single_line_entries_are_counted` fails
#   * make --check rewrite    -> `check_mode_does_not_rewrite` fails
#   * return 0 on mismatch    -> `a_wrong_pin_exits_nonzero` fails
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRIPT="$ROOT/scripts/recount-pinned-inventory.py"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

fail=0
ok()   { printf 'ok    %s\n' "$1"; }
bad()  { printf 'FAIL  %s -- %s\n' "$1" "$2"; fail=1; }

# Build a fixture with `single` single-line entries and `wrapped` wrapped ones,
# declaring `declared` as the pinned size.
fixture() {
  local path="$1" declared="$2" single="$3" wrapped="$4" i
  {
    echo 'fn pinned() {'
    echo "    let expected: [(&str, crate::NameId, &str); ${declared}] = ["
    for ((i = 0; i < single; i++)); do
      echo "        (\"A.short${i}\", p.short${i}, \"theorem\"),"
    done
    for ((i = 0; i < wrapped; i++)); do
      echo '        ('
      echo "            \"A.a_name_long_enough_that_rustfmt_wraps_the_entry_${i}\","
      echo "            p.a_name_long_enough_that_rustfmt_wraps_the_entry_${i},"
      echo '            "theorem",'
      echo '        ),'
    done
    echo '    ];'
    echo '}'
  } > "$path"
}

# --- wrapped entries are counted -------------------------------------------
f="$TMP/wrapped.rs"
# ONLY wrapped entries, so breaking the single-line branch cannot also kill this
# case -- each guard is meant to be isolated by exactly the case that names it.
fixture "$f" 3 0 3
out="$(python3 "$SCRIPT" --check "$f" 2>&1)"; rc=$?
if [ "$rc" -eq 0 ] && [[ "$out" == *"counted=3"* ]] && [[ "$out" == *"wrapped=3"* ]]; then
  ok wrapped_entries_are_counted
else
  bad wrapped_entries_are_counted "expected counted=3 wrapped=3, rc=0; got rc=$rc: $out"
fi

# --- single-line entries are counted ---------------------------------------
f="$TMP/single.rs"
fixture "$f" 4 4 0
out="$(python3 "$SCRIPT" --check "$f" 2>&1)"; rc=$?
if [ "$rc" -eq 0 ] && [[ "$out" == *"counted=4"* ]] && [[ "$out" == *"single=4"* ]]; then
  ok single_line_entries_are_counted
else
  bad single_line_entries_are_counted "expected counted=4 single=4, rc=0; got rc=$rc: $out"
fi

# --- a wrong pin exits nonzero ---------------------------------------------
f="$TMP/wrong.rs"
fixture "$f" 99 3 2          # declares 99, really 5
out="$(python3 "$SCRIPT" --check "$f" 2>&1)"; rc=$?
if [ "$rc" -ne 0 ] && [[ "$out" == *"PIN WRONG"* ]]; then
  ok a_wrong_pin_exits_nonzero
else
  bad a_wrong_pin_exits_nonzero "expected nonzero + PIN WRONG; got rc=$rc: $out"
fi

# --- --check does not rewrite ----------------------------------------------
f="$TMP/nowrite.rs"
fixture "$f" 99 3 2
before="$(cat "$f")"
python3 "$SCRIPT" --check "$f" >/dev/null 2>&1
if [ "$before" = "$(cat "$f")" ]; then
  ok check_mode_does_not_rewrite
else
  bad check_mode_does_not_rewrite "--check modified the file"
fi

# --- the default mode DOES rewrite, to the counted value -------------------
f="$TMP/rewrite.rs"
fixture "$f" 99 3 2
python3 "$SCRIPT" "$f" >/dev/null 2>&1; rc=$?
if [ "$(/usr/bin/grep -c '&str); 5\]' "$f")" -eq 1 ] && [ "$rc" -ne 0 ]; then
  ok default_mode_rewrites_to_the_counted_value
else
  bad default_mode_rewrites_to_the_counted_value "rc=$rc (want nonzero), pin: $(/usr/bin/grep 'let expected' "$f")"
fi

# --- a file with no pinned array is an error, not a zero -------------------
f="$TMP/absent.rs"
echo 'fn nothing() {}' > "$f"
out="$(python3 "$SCRIPT" --check "$f" 2>&1)"; rc=$?
if [ "$rc" -ne 0 ] && [[ "$out" == *"no pinned inventory array"* ]]; then
  ok an_absent_array_is_an_error_not_a_zero
else
  bad an_absent_array_is_an_error_not_a_zero "expected nonzero + diagnostic; got rc=$rc: $out"
fi

# --- every real pinned array in the tree agrees with itself ----------------
#
# `creal_tests.rs` was the ONLY file in the tree matching this pin shape when
# this control was written, and is deliberately no longer one of them: its
# single 432-entry `expected` array was sharded per `creal/` module (one
# `Vec` per file under `creal/inventory/`, no fixed length) precisely because
# a single shared pin collided every pair of concurrent `creal` lanes -- see
# `crates/axeyum-lean-kernel/src/creal/inventory.rs`'s module docs. Recounting
# it here would therefore report "no pinned inventory array found", which is
# the CORRECT answer now, not a regression -- so this control no longer names
# that file specifically and instead checks whatever file(s) in the tree
# still carry this exact pin shape, if any. The tool itself is unchanged and
# remains available to any future `*_tests.rs` that adopts it; the fixture
# cases above are what actually exercise its counting logic.
# Anchored to the start of the (whitespace-stripped) line, NOT a bare
# substring search: `creal/inventory.rs`'s own module docs quote this exact
# pin shape in prose (`//! ... let expected: [(&str, crate::NameId, &str);
# 432] = [ ... ];` explaining why it is gone), and an unanchored grep matches
# that doc line too -- then fails on it as "not terminated by `];`", which is
# the comment ending in prose, not code. `recount-pinned-inventory.py` itself
# has this same blind spot (it also just `.search()`s each line), so the
# anchor here is doing double duty: it is also the right fix for the tool.
mapfile -t pinned_files < <(grep -rlE '^[[:space:]]*let expected: \[\(&str, crate::NameId, &str\); [0-9]+\] = \[' \
  "$ROOT/crates/axeyum-lean-kernel/src" 2>/dev/null)
if [ "${#pinned_files[@]}" -eq 0 ]; then
  ok no_real_file_currently_uses_this_pin_shape
else
  real_fail=0
  for real in "${pinned_files[@]}"; do
    out="$(python3 "$SCRIPT" --check "$real" 2>&1)"; rc=$?
    if [ "$rc" -ne 0 ]; then
      bad the_committed_pin_is_correct "$real: $out"
      real_fail=1
    fi
  done
  [ "$real_fail" -eq 0 ] && ok the_committed_pin_is_correct
fi

[ "$fail" -eq 0 ] && echo "recount-pinned-inventory: all controls pass"
exit "$fail"
