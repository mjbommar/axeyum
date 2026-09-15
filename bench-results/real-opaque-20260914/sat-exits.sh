#!/usr/bin/env bash
# REAL-OPAQUE E1-E4 -- re-derive the `Sat`-exit enumeration MECHANICALLY.
#
# The method is by CONSTRUCTION SITE, not a `?`-scan: ADR-1966 enumerated 72
# refusal-propagation sites and found a `?`-only scan under-reports by half.
# Run from the repository root; writes ref/sat-exits.txt.
set -u
W="$(cd "$(dirname "$0")" && pwd)"
R="$W/ref/sat-exits.txt"
S=crates/axeyum-solver/src

# NOTE: an earlier version of this file stripped test code by cutting each file
# at its FIRST `^#[cfg(test)]` line. In BOTH files that attribute marks a
# test-only helper item in the middle, not the test module at the end, so the
# cut discarded 2,397 and 3,133 lines of PRODUCTION code -- including a whole
# `CheckResult::Sat` construction -- and printed a clean-looking result that was
# a measurement of the accepted subset. Test exclusion is now done by brace
# balance in `satexits.py`, which asserts the shape it cannot handle.

{
echo "== REAL-OPAQUE Sat-exit enumeration =="
echo "commit: $(git rev-parse HEAD)"
echo "date:   $(date -Is)"
echo

echo "-- E0: every cfg(test) attribute, and why a single cut point is wrong --"
for f in "$S/lra.rs" "$S/dpll_lia.rs"; do
  echo "$f  total=$(wc -l < "$f")  cfg(test)_at: $(grep -n '^#\[cfg(test)\]' "$f" | cut -d: -f1 | tr '\n' ' ')"
done
echo "   The FIRST one is a test-only helper item in the middle of both files,"
echo "   not the test module at the end. satexits.py skips each region by brace"
echo "   balance instead, and asserts the shape it cannot handle."
echo

echo "-- E1: every construction site of lra::Collector in the workspace --"
grep -rn 'Collector::default()\|Collector {' --include='*.rs' crates/ \
  | grep -v 'IntCollector\|MembershipCollector\|int_divmod' \
  | grep -v 'struct Collector\|impl Collector'
echo "   (each is either Collector::default() -- allow_opaque_apps == false --"
echo "    or names the field explicitly)"
echo

echo "-- E1b: every mention of the REAL collector's mode in lra.rs --"
echo "   (the integer collector's own, unrelated, pre-existing flag is still"
echo "    spelled allow_opaque_apps and is listed after it for contrast)"
grep -n 'opaque_reals\|OpaqueReals' "$S/lra.rs"
echo "   -- integer side, for contrast --"
grep -n 'allow_opaque_apps' "$S/lra.rs" | head -8
echo

echo "-- E2: callers of collect_constraints_with_options (the only setter) --"
grep -rn 'collect_constraints_with_options(' --include='*.rs' crates/
echo

echo "-- E2b: callers of decide_within_with_options --"
grep -rn 'decide_within_with_options(' --include='*.rs' crates/
echo

echo "-- E3: every Sat CONSTRUCTION in both files, test regions EXCLUDED --"
echo "   (by brace balance, not by cutting at the first cfg(test) -- see satexits.py:"
echo "    the cut version discarded 2,397 + 3,133 production lines and looked clean)"
python3 "$W/satexits.py" "$S/lra.rs" "$S/dpll_lia.rs"
echo

echo "-- E3c: the guards that close them --"
grep -n 'has_opaque_vars()' "$S/lra.rs"
grep -n 'has_opaque_real_apps\|has_opaque_int_apps' "$S/dpll_lia.rs"
echo

echo "-- E4: the real-theory consumers in dpll_lia.rs (whole file) --"
grep -n 'real_theory_oracle\|real_model_oracle\|atom_in_lra_opaque_fragment\|atom_in_lra_fragment\|check_with_lra' "$S/dpll_lia.rs"
echo

echo "-- E4b: every sat exit of the dpll_lia refinement loop --"
grep -n 'try_finish_sat(\|finish_sat(' "$S/dpll_lia.rs" | grep -v 'fn \|///'
echo
} > "$R" 2>&1
echo "wrote $R"
wc -l "$R"
