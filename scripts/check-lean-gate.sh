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
#
# Raised 109 -> 111 on 2026-08-15 by lane `import-wfrec`:
# `real_lean_local_let_zeta_crosscheck` adds two more, checking that official
# Lean agrees with this kernel's verdicts on local-`let` (ζ) reduction — the
# rule whose absence inside the lazy-delta loop refused `Nat.bitwise._unary`,
# the top declined root in both scale censuses. The positive module also asserts
# that the `letE` survives elaboration, so a toolchain that zeta-expands early
# fails the suite instead of making it vacuous. Fifteen suites now;
# measured total 122 (52 tests) — the two new ones plus three that
# `lean_crosscheck`'s representative slice picked up since 2026-08-15.
#
# Raised 111 -> 115 on 2026-08-15 by lane `import-projrec`:
# `real_lean_structure_eta_recursor_crosscheck` adds FOUR — one positive module
# and three refusals, one per claim, because Lean keeps elaborating after an
# error and three failures in one module would be indistinguishable from one.
# It checks that official Lean agrees on structure-eta reduction of a *stuck*
# recursor major premise (`to_cnstr_when_structure`), the rule whose absence
# refused `Nat.Linear.Poly.denote_reverse` — the top declined root in both scale
# censuses after ζ landed. The positive module reads `#print axioms` back and
# fails on `sorryAx`, so an admitted goal cannot read as agreement. Sixteen
# suites now; measured total 126 (53 tests). SEVENTEEN since 2026-08-17:
# `real_lean_wire_differential` adds 93 (92 wire mutants plus the undamaged
# development) and is the first check in the ADVERSARIAL direction -- it asks
# whether OUR kernel admits anything Lean's refuses, and on its first run it
# found one (`tc.rs` `check_core` skipped the sort check on a lambda binder
# domain). Measured total 219 (56 tests).
CHECK_FLOOR="${AXEYUM_LEAN_CHECK_FLOOR:-208}"

# The total above counts modules Lean READ. It is not a count of propositions
# Lean PROVED, and the gap is large: measured 2026-08-17, 41 of `lean_crosscheck`'s
# 74 families emit a STRUCTURAL ATTESTATION -- `axiom prop : Prop`, `axiom hyp1 :
# prop`, `axiom hyp2 : Not prop`, then `False` by application. Lean accepts that
# trivially and its acceptance says nothing about the proposition. The emitter
# takes no arena and no assertions, so its output cannot depend on the query at
# all.
#
# `qf_bv` is one of the 41, which is worth understanding rather than deploring:
# `scan_ground_bv_proof_fragment` prefers `term_level_enum_certifies` to
# `ProofFragment::QfBv`, and exhaustive term-level evaluation is the STRONGER
# Rust-side certificate -- it trusts neither the bit-blaster, the CNF encoder,
# nor the SAT solver. It simply has no theory Lean module. That family uses
# `BitVec(2)`, and the crossover for its shape sits between 8 and 16 bits, so it
# never reaches bit-blasting at all. The `qf_bv_wide` family added alongside it
# runs the same theorem at `BitVec(16)`, where the reconstruction is the
# bit-level one the name always implied -- which is why the reasoning floor was
# 33 and not 32. Raised to 34 on 2026-08-17 when `qf_rdl_difference` was added:
# the representative slice is one module per FAMILY and real difference logic
# scans into the `Lra` family, so no module from the QF_RDL *logic* had ever been
# handed to `lean` -- and it reconstructs rather than attests.
#
# So this gate reports the two halves separately, and floors the half that is
# actually reasoning. Flooring only the sum lets theory families be replaced by
# attestations with the headline unmoved. `lean_crosscheck` prints the split as
# LEAN_CONTENT_SUMMARY (it classifies each rendered module by its own header
# marker, needing no Lean binary); this reads that line.
THEORY_FAMILY_FLOOR="${AXEYUM_LEAN_THEORY_FLOOR:-37}"

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
axeyum-lean-kernel||real_lean_local_let_zeta_crosscheck
axeyum-lean-kernel||real_lean_structure_eta_recursor_crosscheck
axeyum-lean-kernel||real_lean_structure_eta_crosscheck
axeyum-lean-kernel||real_lean_compact_share_crosscheck
axeyum-lean-kernel||real_lean_kernel_replay
axeyum-lean-import||real_lean_wire_differential
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
content_summary=""

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
  if grep -q 'LEAN_CONTENT_SUMMARY|' "$log"; then
    content_summary=$(grep -o 'LEAN_CONTENT_SUMMARY|.*' "$log" | tail -1)
  fi

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

# The content split. Absence is a failure, not a pass: if `lean_crosscheck` ran
# and printed no summary, this gate has stopped being able to tell reasoning
# from attestation, and silently reporting only the total is exactly the
# overstatement the split exists to prevent.
if [ -z "$content_summary" ]; then
  echo "check-lean-gate: no LEAN_CONTENT_SUMMARY was printed, so the reasoning/attestation" \
       "split could not be read. That is a failure: the total above counts modules Lean READ," \
       "and without the split it reads as modules Lean PROVED." >&2
  fail=1
else
  theory_families=$(sed -n 's/.*|theory_families=\([0-9]*\).*/\1/p' <<<"$content_summary")
  structural_families=$(sed -n 's/.*|structural_families=\([0-9]*\).*/\1/p' <<<"$content_summary")
  # A summary that is present but unparseable is the same failure as an absent
  # one, and worse if unnoticed: empty fields would make the arithmetic below
  # print a confident wrong split. Fail on the parse, not on its consequences.
  if [ -z "$theory_families" ] || [ -z "$structural_families" ]; then
    echo "check-lean-gate: LEAN_CONTENT_SUMMARY was printed but its theory/structural fields" \
         "could not be parsed, so the split is unknown. The line was: $content_summary" >&2
    fail=1
    theory_families=0
    structural_families=0
  fi
  echo "check-lean-gate: crosscheck content: $theory_families families carry a theory" \
       "reconstruction, $structural_families are structural attestations (an axiom pair Lean" \
       "accepts trivially) -- floor $THEORY_FAMILY_FLOOR on the reasoning half"
  if [ "${theory_families:-0}" -lt "$THEORY_FAMILY_FLOOR" ]; then
    echo "check-lean-gate: only $theory_families families carry a theory reconstruction, below" \
         "the committed floor of $THEORY_FAMILY_FLOOR. Reasoning has been replaced by" \
         "attestation somewhere; the total check count would not have moved. If deliberate," \
         "lower THEORY_FAMILY_FLOOR in this file and say why." >&2
    fail=1
  fi
fi

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
echo "check-lean-gate: OK -- $total_checked modules/controls were READ by a real Lean kernel" \
     "($structural_families of $((theory_families + structural_families)) crosscheck families are" \
     "attestations, so this is not a count of propositions proved)"
