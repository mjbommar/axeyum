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

# ===========================================================================
# Controls for the OTHER THREE SHAPES (2026-08-29).
#
# The tool used to recognize `let expected: [(&str, crate::NameId, &str); N]`
# and nothing else, so it answered "no pinned inventory array found" for the
# `[crate::NameId; N]` site whose merge it was run against. The counting engine
# is now shape-independent: mask comments/strings/chars, then split the array
# literal on TOP-LEVEL commas.
#
# MEASURED kill matrix (2026-08-29), each mutant applied to a copytree'd scratch
# copy -- never to the tracked script, because a mutated source on disk is
# indistinguishable from a wrong one to every other lane compiling from it:
#
#   mutation                                   dedicated fixture killer
#   drop the `masked[j] != "["` site check  -> a_bare_type_annotation_is_not_a_pin
#   drop `{` from _BRIDGE                   -> a_function_return_position_pin_is_counted
#   blank strings WHOLE instead of inner    -> string_entries_are_counted_once_each
#   skip line-comment masking               -> comments_between_entries_are_not_entries
#   rewrite edits front-to-back             -> every_wrong_pin_in_one_file_is_rewritten
#   measure single/wrapped on `src`         -> a_commented_entry_is_not_wrapped
#
# Two things that matrix does NOT claim, both deliberate:
#
#   * The first four are ALSO killed by `the_committed_pins_in_the_tree_are_correct`.
#     That is a backstop, not a duplicate: it discriminates only as long as the
#     named files keep the shapes they have today, so it can silently stop
#     covering a guard while staying green. The fixtures are what actually pin
#     each guard; the tree control is what catches a shape nobody wrote a
#     fixture for.
#   * Dropping comment masking kills BOTH comment cases. That is a real
#     dependency rather than a redundancy -- measuring single/wrapped on masked
#     text presupposes that comments are masked at all -- so there is no fixture
#     that separates them, and inventing one would mean weakening the second
#     until it stopped testing its own guard. The reverse direction IS clean:
#     measuring single/wrapped on `src` kills only `a_commented_entry_is_not_wrapped`.
#
# The `const`/`let` versus function-return-position split across the fixtures
# below is load-bearing, not stylistic: when every fixture used the return
# form, dropping `{` from `_BRIDGE` killed four cases at once and the
# function-return guard had no unique killer.

# --- a bare `[crate::NameId; N]` in return position is counted --------------
#
# THE SITE THAT MOTIVATED THIS: `int_prelude_tests.rs`'s `derived_laws`. The
# entries are `p.field,` one per line -- no `("` anywhere -- and the pin is in
# a function's RETURN TYPE, not a `let`.
f="$TMP/nameid_return.rs"
cat > "$f" <<'EOF'
/// Doc comment with a deliberately unbalanced range like [0,n) and a [`link`].
fn derived_laws(p: &IntPrelude) -> [crate::NameId; 3] {
    [
        p.first,
        p.second,
        p.third,
    ]
}
EOF
out="$(python3 "$SCRIPT" --check "$f" 2>&1)"; rc=$?
if [ "$rc" -eq 0 ] && [[ "$out" == *"counted=3"* ]] && [[ "$out" == *"crate::NameId"* ]]; then
  ok a_function_return_position_pin_is_counted
else
  bad a_function_return_position_pin_is_counted "expected counted=3 for [crate::NameId; 3], rc=0; got rc=$rc: $out"
fi

# --- a `[T; N]` that is only a TYPE is not a pin ----------------------------
#
# Without the "the next non-bridge character must be `[`" check, every array
# type annotation in the tree becomes a site and the tool reports a count for a
# literal that is not there.
f="$TMP/type_only.rs"
cat > "$f" <<'EOF'
fn takes(xs: [crate::NameId; 4]) -> usize {
    xs.len()
}
EOF
out="$(python3 "$SCRIPT" --check "$f" 2>&1)"; rc=$?
if [ "$rc" -ne 0 ] && [[ "$out" == *"no pinned inventory array"* ]]; then
  ok a_bare_type_annotation_is_not_a_pin
else
  bad a_bare_type_annotation_is_not_a_pin "expected nonzero + diagnostic; got rc=$rc: $out"
fi

# --- `[&str; N]` entries count once each -----------------------------------
#
# Discriminates BOTH directions of the string guard in one fixture, so the
# guard has exactly one killer:
#   * strings not masked at all -> the comma inside "a,b" splits it, counted=3
#   * strings blanked WHOLE     -> every entry is whitespace and dropped, counted=0
# Only "mask the CONTENT, keep the delimiters" gives 2. The `]` inside the
# second literal also proves brackets are not fed to the depth counter.
f="$TMP/strs.rs"
cat > "$f" <<'EOF'
const NAMES: [&str; 2] = ["a,b", "c]d"];
EOF
out="$(python3 "$SCRIPT" --check "$f" 2>&1)"; rc=$?
if [ "$rc" -eq 0 ] && [[ "$out" == *"counted=2"* ]]; then
  ok string_entries_are_counted_once_each
else
  bad string_entries_are_counted_once_each "expected counted=2, rc=0; got rc=$rc: $out"
fi

# --- comments between entries are not entries ------------------------------
#
# `int_prelude_tests.rs` really does interleave a four-line `//` block inside
# `derived_lemmas`. Unmasked, the `'` in "anyone's" opens a char literal that
# swallows the rest of the file, and the `(` in the prose unbalances the depth
# counter -- either of which changes the count.
f="$TMP/commented.rs"
cat > "$f" <<'EOF'
const LEMMAS: [crate::NameId; 2] = [
    P.first,
    // Found by the coverage assertion, not by anyone's noticing: this
    // one (and only this one) was live and unlisted.
    P.second,
];
EOF
out="$(python3 "$SCRIPT" --check "$f" 2>&1)"; rc=$?
if [ "$rc" -eq 0 ] && [[ "$out" == *"counted=2"* ]]; then
  ok comments_between_entries_are_not_entries
else
  bad comments_between_entries_are_not_entries "expected counted=2, rc=0; got rc=$rc: $out"
fi

# --- a commented entry is SINGLE, not WRAPPED ------------------------------
#
# `wrapped` names the measured failure (rustfmt splitting a long entry across
# five lines), so it must not also fire for an entry that merely has a comment
# above it -- `derived_lemmas` reported wrapped=1 for exactly that reason and
# nothing in it is wrapped. Measured on the MASKED text, not on the source.
f="$TMP/single_after_comment.rs"
cat > "$f" <<'EOF'
const LEMMAS: [crate::NameId; 2] = [
    P.first,
    // a comment spanning
    // two lines
    P.second,
];
EOF
out="$(python3 "$SCRIPT" --check "$f" 2>&1)"; rc=$?
if [ "$rc" -eq 0 ] && [[ "$out" == *"single=2"* ]] && [[ "$out" == *"wrapped=0"* ]]; then
  ok a_commented_entry_is_not_wrapped
else
  bad a_commented_entry_is_not_wrapped "expected single=2 wrapped=0; got rc=$rc: $out"
fi

# --- every pin in a multi-pin file is rewritten, to its own value -----------
#
# `int_prelude_tests.rs` carries FOUR. Rewriting front-to-back invalidates every
# later offset as soon as one pin's digit count changes (9 -> 10 here), so a
# later pin's digits get overwritten in the wrong place; back-to-front keeps
# them valid. Also pins that a CORRECT pin in the same file is left alone.
f="$TMP/multi.rs"
cat > "$f" <<'EOF'
const A: [crate::NameId; 9] = [
    P.a1, P.a2, P.a3, P.a4, P.a5,
    P.a6, P.a7, P.a8, P.a9, P.a10,
];
const B: [crate::NameId; 2] = [P.b1, P.b2];
const C: [crate::NameId; 5] = [P.c1, P.c2, P.c3];
EOF
python3 "$SCRIPT" "$f" >/dev/null 2>&1; rc=$?
got_a="$(/usr/bin/grep -c 'const A: \[crate::NameId; 10\]' "$f")"
got_b="$(/usr/bin/grep -c 'const B: \[crate::NameId; 2\]' "$f")"
got_c="$(/usr/bin/grep -c 'const C: \[crate::NameId; 3\]' "$f")"
if [ "$rc" -ne 0 ] && [ "$got_a" -eq 1 ] && [ "$got_b" -eq 1 ] && [ "$got_c" -eq 1 ]; then
  ok every_wrong_pin_in_one_file_is_rewritten
else
  bad every_wrong_pin_in_one_file_is_rewritten \
    "rc=$rc (want nonzero) a=$got_a b=$got_b c=$got_c"
fi

# --- every pinned array in the tree agrees with itself ----------------------
#
# The tree COMPILES, so every pin in it is correct by construction -- which
# makes this a check on the TOOL, not on the tree: a counting engine wrong
# about any real shape reports a false PIN WRONG here. It is not a vacuous
# pass, because `a_wrong_pin_exits_nonzero` above pins that the tool can say
# PIN WRONG at all. Scoped to the files whose pins lanes actually grow, plus
# `ordered_ring.rs`, whose two `[&str; N]` tables are the widest real
# string-shaped pins in the tree.
tree_fail=0
for real in \
  "$ROOT/crates/axeyum-lean-kernel/src/int_prelude/int_prelude_tests.rs" \
  "$ROOT/crates/axeyum-lean-kernel/src/complex/complex_tests.rs" \
  "$ROOT/crates/axeyum-solver/src/reconstruct/arithmetic/ordered_ring.rs"
do
  [ -f "$real" ] || continue
  out="$(python3 "$SCRIPT" --check "$real" 2>&1)"; rc=$?
  if [ "$rc" -ne 0 ]; then
    bad the_committed_pins_in_the_tree_are_correct "$real: $out"
    tree_fail=1
  fi
done
[ "$tree_fail" -eq 0 ] && ok the_committed_pins_in_the_tree_are_correct

[ "$fail" -eq 0 ] && echo "recount-pinned-inventory: all controls pass"
exit "$fail"
