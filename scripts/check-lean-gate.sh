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
#   1. RESOLVES the PINNED toolchain — the one `lean-toolchain` names — by the
#      same policy as `crates/axeyum-lean-kernel/tests/support/lean_probe.rs`,
#      and then CROSS-CHECKS that every suite reported using that same binary.
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
#   scripts/check-lean-gate.sh              # resolve, require, count, enforce
#   scripts/check-lean-gate.sh --print-toolchain  # resolve and stop (see below)
#   AXEYUM_LEAN_BIN=/path/to/lean  …        # explicit override (authoritative)
#   AXEYUM_ALLOW_NO_LEAN=1         …        # no toolchain -> loud SKIP, exit 0
#   AXEYUM_LEAN_ALLOW_UNPINNED=1   …        # state a deliberate non-pinned run
#
# Negative controls for this gate: scripts/tests/test-lean-toolchain-policy.sh
#
# NO TOOLCHAIN IS A FAILURE BY DEFAULT. That is deliberate: the whole incident
# above is what "absent Lean quietly passes" looks like. A machine that genuinely
# has no Lean sets `AXEYUM_ALLOW_NO_LEAN=1` and gets a banner saying, in words,
# that zero Lean checks ran.
#
# ---------------------------------------------------------------------------
# WHICH Lean, and why that is a soundness question rather than a setup detail
# ---------------------------------------------------------------------------
#
# The fix above left a second, quieter defect: it said WHETHER a Lean ran, never
# WHICH. Measured on the development host on 2026-08-17 with two toolchains
# installed (v4.30.0 and v4.34.0-rc1), the shell gate and the Rust probe carried
# two hand-written copies of the search order and DISAGREED — this script tried
# `command -v lean` first and found elan's default (4.30.0), while the probe
# sorted elan's toolchain directories newest-name-first and took 4.34.0-rc1.
# Under 4.34, 21 of 77 `lean_crosscheck` families were rejected while all 77
# passed under 4.30, and `scripts/lean/replay-lean4export.lean` did not even
# elaborate. So the gate's verdict depended on which toolchain happened to be
# installed and on which entry point ran, and nothing in its output named the
# checker that produced it.
#
# The policy is now ONE policy, implemented in `lean_probe.rs` and mirrored here
# line for line: **the pin runs**. `lean-toolchain` at the repository root is the
# pin; resolution is AXEYUM_LEAN_BIN (authoritative in both directions), then the
# pinned toolchain's own elan directory, then PATH / other elan toolchains / the
# elan shim ONLY IF `--version` matches the pin. There is no "newest wins" step:
# a host with only a non-pinned Lean resolves nothing and says so.
#
# It is the pin and not the newest because several suites are frozen-source
# reproductions that assert an exact toolchain — `real_lean_strict_positivity_
# crosscheck` asserts commit d024af099ca4bf2c86f649261ebf59565dc8c622, and
# `real_lean_wire_differential` is a differential against the reference
# implementation, which means nothing against "whatever was installed". Moving to
# a newer Lean is an explicit act: edit `lean-toolchain`, and every entry point
# follows in one commit.
#
# `AXEYUM_LEAN_ALLOW_UNPINNED=1` states a deliberate deviation; it relaxes the
# assertion, never the search, and the mismatch is still printed on every line.
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2

# The floor. Measured 2026-08-14 on Lean 4.30.0: 112 real-Lean invocations across
# the twelve suites below (kernel side 21, solver side 91 — of which 70 are
# `lean_crosscheck`'s one-module-per-family representative slice). Set with
# headroom so ordinary churn does not trip it; RAISING it as suites grow is the
# ratchet working, LOWERING it needs a reason in the commit message.
#
# Raised 261 -> 278 on 2026-09-05 by lane `lean-replay-census-all` (ADR-1661,
# item 2 of the Next Ten in `docs/math-department/14-lean-lang.md`):
# `real_lean_replay_census_all` adds SEVENTEEN real-Lean invocations, one per
# carrier. `real_lean_replay_census` (ADR-0760) graded independent replay per
# declaration over the constructed reals only; this extends the same harness --
# `tests/support/replay_census.rs`, shared by both suites so they cannot drift --
# to every other carrier the kernel builds, plus one `everything` carrier that
# builds them all into ONE kernel so a headline is a union rather than a sum of
# nesting rows. Measured that day on pinned Lean 4.34.0-rc1: `everything`
# population 4,458, representable 4,374, replayed 4,374, `missing=0 extra=0`,
# with 50 `Theorem`s whose type is not a `Prop` (which Lean's kernel refuses as
# theorems) and 34 blocked behind one of those. Sixteen of the seventeen come
# from `CARRIERS`; the three non-Lean tests in that suite (the builder-coverage
# guard and two classifier controls) contribute none.
#
# Raised 229 -> 261 on 2026-08-30 by lane `l0-s5-kernel-differential` (S5 of the
# ADR-0717 safety roadmap): `kernel_differential` adds THIRTY-TWO real-Lean
# invocations, one per corpus case across all eight named subsystems
# (conversion, universes, inductives, recursors, projections, literals,
# quotient, proof irrelevance). Unlike the `real_lean_*_crosscheck` suites,
# every case is authored TWICE, independently -- once via this crate's kernel
# term-builder API, once as plain Lean surface syntax -- because
# `Kernel::render_lean_module` only walks an already-admitted closure and so
# cannot express the nearly-well-typed half of the corpus (a rejected
# declaration never reaches `environment()`). Measured that day: 32/32 cases,
# `checked=32`, zero unexplained accept/reject disagreement, one registered
# incompleteness (`quotient::quot_sound_absent` -- this kernel has no
# `Quot.sound` by design, ADR-0456). See ADR-0780 and
# `artifacts/kernel-differential/mutant-kill-table.json` for the accompanying
# kernel-source mutation pass (4 of 8 targeted guards killed).
#
# Raised 223 -> 229 on 2026-08-30 by lane `l0-s4-independent-replay` (S4 of the
# ADR-0717 safety roadmap): `real_lean_replay_census` adds SIX real-Lean
# invocations. It is the first check that grades independent replay PER
# DECLARATION rather than per carrier count -- `replay-lean4export.lean
# --emit-names` reads back the constant names Lean's own kernel ended holding,
# so a subject is graded by membership of its own name and cannot inherit a
# grade from a sampled sibling. Measured that day: population 2,045,
# representable 1,972, `checked=1972 expected=1972 missing=0 extra=0`, and 73
# declarations non-representable with a typed reason (48 `Theorem`s whose type
# is not a `Prop`, which Lean's kernel refuses outright, and 25 blocked by
# depending on one). Its six invocations are: the census slice, the earned
# typed reason, the sampled-family inheritance guard, and a clean/wrong-proof/
# wrong-goal triple on `CReal.ivt_approx`.
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
#
# Raised 208 -> 212 on 2026-08-18 by lane `lean-prelude-module`:
# `real_lean_shared_prelude_crosscheck` adds FOUR, and it is the first suite that
# hands Lean a module set rather than a module -- a shared development compiled
# to an `.olean` plus a query module that `import`s it (ADR-0511). Two of the
# four are negative controls, because the positive result is otherwise
# indistinguishable from an import that did nothing: the query module checked
# with `LEAN_PATH=""` must FAIL, and a module that re-declares what its import
# supplies must FAIL. Eighteen suites now.
#
# Raised 212 -> 218 on 2026-08-18 by lane `creal-lean-divergence`:
# `real_lean_creal_carrier_kernel_replay` adds TWO and is the first check that
# hands Lean the WHOLE carrier -- all 470 declarations of `build_creal_prelude`,
# with no reachability filter. Every other suite renders the closure of one
# refutation, so Lean had only ever seen the declarations some query cited (343
# of 465 when ADR-0511's lane measured it); the other 122 had never been handed
# to any Lean, and the first time anything pointed Lean at them two were
# refused. It replays through
# `Environment.addDeclCore` -- Lean's KERNEL -- which accepts all 470 in 1.4 s,
# and its exit status depends on Lean's reported constant count EQUALLING the
# count read out of our kernel, so "accepted" cannot mean "accepted a subset".
# CORRECTED 2026-08-30 (see the 229 -> 230 entry below and ADR-0775): "accepts
# all 470" is FALSE and was never re-derivable -- the suite SIGABRTed before
# reaching Lean from the day after this paragraph was written. Lean's kernel
# refuses a `theorem` whose type is not a `Prop`, and 73 of the carrier's 2,058
# declarations are of that shape or depend on one. The count equality is now
# against the REPRESENTABLE population, and Lean is required to reject the
# unfiltered stream.
# `real_lean_wellfounded_elaborator_divergence` adds FOUR and names the residue
# the source route leaves: Lean's ELABORATOR does not unfold a `theorem` while
# reducing, so `Nat.gcd 2 4 = 2` is refused where the structurally recursive
# `Nat.mod 4 2 = 0` is accepted and Lean's kernel takes both (ADR-0517). Two of
# the four are controls -- the `mod` module, without which the refusal would be
# a statement about module size, and the SAME gcd module with every `theorem`
# re-spelled `def`, which Lean accepts and which isolates the mechanism to one
# token per line. Twenty suites now.
#
# Raised 218 -> 219 on 2026-08-19 by lane `agent-prepush-scope`:
# `real_lean_string_monoid_crosscheck` adds ONE, and it was not in this table at
# all -- it landed on 2026-08-17 and only `hooks/pre-push`'s wholesale
# `cargo test -p axeyum-lean-kernel` ever ran it, which counts nothing, enforces
# no pin and cannot tell a skip from a pass. It also printed its marker as
# `AXEYUM-LEAN-CHECKED|string-monoid|1|...`, which this script's parser
# (`AXEYUM-LEAN-CHECKED <tag> checked=<n>`) reads as zero, so listing it without
# fixing that would have failed with `0-lean-checks`; it now calls
# `lean_probe::report_checked`. The check is Lean's own `#print axioms` on an
# exported string-monoid theorem: every opaque word present, and nothing from the
# string prelude -- `append` was a `Declaration::Axiom` until 2026-08-17, and an
# axiom is exactly what an external checker accepts vacuously. Twenty-one suites
# now. Found by `scripts/check-kernel-suites.sh`, which asserts that every
# `crates/axeyum-lean-kernel/tests/*.rs` is in exactly one of {runs at push time,
# owned by this gate}.
#
# Raised 219 -> 223 on 2026-08-30 by lane `golden-lean-check`: FOUR of the five
# quantifier golden-pin suites (`quant_affine_growth_lean`,
# `quant_counterexample_cover`, `quant_eq_partition_lean`,
# `quant_residue_lean`) carried a byte pin over their rendered module and
# nothing else -- a pin says the bytes match a blessed hash, never that a real
# `lean` binary still accepts them. Only `diophantine_lean_reconstruct` (already
# listed above) had a genuine real-Lean check. Each of the four now has a
# `*_module_checks_in_real_lean` test following diophantine's exact pattern:
# write the module, run the pinned toolchain via `lean_probe`, assert exit 0,
# assert no `sorryAx` in the `#print axioms axeyum_refutation` output. Each
# reports exactly one real-Lean check, so +4. Doctored-module negative control
# run manually against all five (this suite included) before landing: flipping
# the theorem's stated type from `False` to `True` makes Lean reject every one
# with a type mismatch, exit 1 -- so this check can fail.
# Raised 229 -> 230 on 2026-08-30 by lane `carrier-replay-overclaim`:
# `real_lean_creal_carrier_kernel_replay` goes from TWO real-Lean checks to
# THREE. Its whole-carrier claim was FALSE -- Lean's kernel refuses a `theorem`
# whose type is not a `Prop`, and this kernel admits 48 of them plus 25 that
# depend on one, so 73 of 2,058 declarations were never independently replayed
# and nothing said so. The suite now hands Lean the representable population
# (1,985, count equality enforced), the TAMPERED representable stream, and --
# the new third invocation -- the UNFILTERED export, which Lean must REJECT
# naming a declaration this kernel independently classified as
# not-a-proposition. That third run is what makes the narrowing a rule of
# Lean's rather than a convenience of ours, and it is the superseded claim kept
# executable (ADR-0775).
#
# The suite reached no verdict at all between 2026-08-18 and 2026-08-30: it
# SIGABRTed on a 2 MiB `#[test]` stack before a single Lean ran. Measured while
# fixing this, by reproducing the crash: zero `AXEYUM-LEAN-TOOLCHAIN` banners
# and zero `AXEYUM-LEAN-CHECKED` markers, so THIS gate fails it three ways
# (nonzero cargo status, `unnamed-toolchain`, `0-lean-checks`) and the fact's
# own `checker_command` exits 101. The guards were fail-closed; nobody ran
# them. `AXEYUM_REQUIRE_LEAN=1` does NOT catch it -- it fires only when a
# toolchain cannot be resolved, and the abort happens before the probe.
CHECK_FLOOR="${AXEYUM_LEAN_CHECK_FLOOR:-278}"

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
axeyum-lean-kernel||real_lean_string_monoid_crosscheck
axeyum-lean-kernel||real_lean_compact_share_crosscheck
axeyum-lean-kernel||real_lean_shared_prelude_crosscheck
axeyum-lean-kernel||real_lean_kernel_replay
axeyum-lean-kernel||real_lean_creal_carrier_kernel_replay
axeyum-lean-kernel||real_lean_replay_census
axeyum-lean-kernel||real_lean_replay_census_all
axeyum-lean-kernel||real_lean_wellfounded_elaborator_divergence
axeyum-lean-kernel||kernel_differential
axeyum-lean-import||real_lean_wire_differential
axeyum-solver|full|int_inequality_lean_reconstruct
axeyum-solver|full|lean_module_fixtures
axeyum-solver|full|diophantine_lean_reconstruct
axeyum-solver|full|quant_affine_growth_lean
axeyum-solver|full|quant_counterexample_cover
axeyum-solver|full|quant_eq_partition_lean
axeyum-solver|full|quant_residue_lean
axeyum-solver|full|regex_emptiness_lean_reconstruct
axeyum-solver|full|lean_crosscheck
EOF
)

# ---------------------------------------------------------------------------
# Resolution. Mirrors `lean_probe::lean_bin` step for step. The two must agree,
# and the cross-check further down PROVES they did on this run rather than
# trusting that this comment stayed true.
# ---------------------------------------------------------------------------
pinned_toolchain=$(tr -d '[:space:]' <lean-toolchain 2>/dev/null)
if [ -z "$pinned_toolchain" ]; then
  echo "check-lean-gate: FAILED -- no readable \`lean-toolchain\` at the repository root, so" \
       "there is no pin to resolve and any Lean found would be an unstated environment fact." >&2
  exit 1
fi
# `leanprover/lean4:v4.30.0` -> `4.30.0`, and elan's directory spelling.
pinned_version="${pinned_toolchain##*:v}"
pinned_directory=$(printf '%s' "$pinned_toolchain" | sed 's|/|--|g; s|:|---|g')

# Matched with the trailing comma `lean --version` prints, so `4.30.0` cannot
# match `4.30.0-rc1` and `4.3` cannot match `4.30.0`.
version_matches_pin() { case "$1" in *"version $pinned_version,"*) return 0 ;; *) return 1 ;; esac; }

# Sorted and de-duplicated, byte-wise, so this emits the SAME order as
# `lean_probe::elan_roots` (which sorts a `Vec<PathBuf>`). Two roots can name one
# binary here -- `~/.elan/toolchains` is a symlink to `~/.elan/elan-home/toolchains`
# on hosts provisioned by `scripts/install-pinned-lean.sh` -- and an order that
# differed between the two implementations made them print two different PATHS
# for the same Lean, which the cross-check below would have read as a mismatch.
elan_roots() {
  {
    [ -n "${ELAN_HOME:-}" ] && printf '%s\n' "$ELAN_HOME"
    [ -n "${HOME:-}" ] && printf '%s\n%s\n' "$HOME/.elan/elan-home" "$HOME/.elan"
  } | LC_ALL=C sort -u
}

# Candidates in POLICY order, one per line. The pinned toolchain's own directory
# first; everything after it must still pass the version check.
lean_candidates() {
  local root
  while IFS= read -r root; do
    [ -x "$root/toolchains/$pinned_directory/bin/lean" ] &&
      printf '%s|elan-pinned-toolchain\n' "$root/toolchains/$pinned_directory/bin/lean"
  done < <(elan_roots)
  local candidate
  candidate=$(command -v lean 2>/dev/null) && printf '%s|PATH\n' "$candidate"
  local toolchain
  while IFS= read -r root; do
    [ -d "$root/toolchains" ] || continue
    while IFS= read -r toolchain; do
      [ "$(basename "$toolchain")" = "$pinned_directory" ] && continue
      [ -x "$toolchain/bin/lean" ] && printf '%s|elan-other-toolchain\n' "$toolchain/bin/lean"
    done < <(find "$root/toolchains" -mindepth 1 -maxdepth 1 -type d | LC_ALL=C sort)
    [ -x "$root/bin/lean" ] && printf '%s|elan-shim\n' "$root/bin/lean"
  done < <(elan_roots)
}

# An explicit `AXEYUM_LEAN_BIN` is authoritative in BOTH directions: if it is set
# and does not resolve we do NOT search on, or `AXEYUM_LEAN_BIN=/nonexistent`
# (the negative control for this gate) would quietly find an elan toolchain and
# prove nothing.
lean=""
lean_source=""
lean_version=""
if [ -n "${AXEYUM_LEAN_BIN:-}" ]; then
  if [ -x "$AXEYUM_LEAN_BIN" ]; then
    lean="$AXEYUM_LEAN_BIN"
    lean_source="AXEYUM_LEAN_BIN"
    lean_version=$("$lean" --version 2>&1 | head -1)
  fi
else
  while IFS='|' read -r candidate source; do
    [ -n "$candidate" ] || continue
    candidate_version=$("$candidate" --version 2>/dev/null | head -1)
    [ -n "$candidate_version" ] || continue
    if version_matches_pin "$candidate_version"; then
      lean="$candidate"
      lean_source="$source"
      lean_version="$candidate_version"
      break
    fi
  done < <(lean_candidates)
fi

if [ -z "$lean" ]; then
  echo "check-lean-gate: no Lean matching the pin. policy=pinned; lean-toolchain=$pinned_toolchain;" \
       "AXEYUM_LEAN_BIN='${AXEYUM_LEAN_BIN:-<unset>}'; candidates considered:" >&2
  while IFS='|' read -r candidate source; do
    [ -n "$candidate" ] || continue
    echo "check-lean-gate:   $candidate ($source) [$("$candidate" --version 2>&1 | head -1)]" >&2
  done < <(lean_candidates)
  if [ "${AXEYUM_ALLOW_NO_LEAN:-}" = "1" ]; then
    echo "check-lean-gate: SKIPPED -- 0 real-Lean checks ran. This is NOT a pass;" \
         "AXEYUM_ALLOW_NO_LEAN=1 was set, so nothing external read our exported modules." >&2
    exit 0
  fi
  echo "check-lean-gate: FAILED. Install the PINNED toolchain" \
       "(\`elan toolchain install $pinned_toolchain\`), point AXEYUM_LEAN_BIN at a \`lean\`, or set" \
       "AXEYUM_ALLOW_NO_LEAN=1 to accept a run in which ZERO Lean checks happen. A newer Lean that" \
       "is already installed is deliberately NOT used: see the policy note at the top of this file." >&2
  exit 1
fi

echo "check-lean-gate: pin $pinned_toolchain (from lean-toolchain)"
echo "check-lean-gate: using $lean (via $lean_source)"
echo "check-lean-gate: $lean_version"

if version_matches_pin "$lean_version"; then
  echo "check-lean-gate: toolchain matches the pin"
elif [ "${AXEYUM_LEAN_ALLOW_UNPINNED:-}" = "1" ]; then
  echo "check-lean-gate: WARNING -- the resolved Lean is NOT the pinned $pinned_version." \
       "AXEYUM_LEAN_ALLOW_UNPINNED=1 was set, so this run is accepted; every claim it produces is" \
       "about $lean_version, not about the pin." >&2
else
  echo "check-lean-gate: FAILED -- TOOLCHAIN MISMATCH. \`lean-toolchain\` pins $pinned_toolchain" \
       "but the resolved Lean is: $lean_version ($lean, via $lean_source). Suites here include" \
       "frozen-source reproductions that assert an exact toolchain, so a different Lean changes" \
       "WHAT is checked, not just whether it passes. Set AXEYUM_LEAN_ALLOW_UNPINNED=1 to state the" \
       "deviation deliberately." >&2
  exit 1
fi

lean_real=$(readlink -f "$lean" 2>/dev/null || printf '%s' "$lean")

# `--print-toolchain` resolves and stops. `scripts/tests/test-lean-toolchain-policy.sh`
# uses it to compare THIS implementation's answer against the Rust probe's, which
# is the only way to know the two agree on a given host -- a comment claiming they
# mirror each other is what was true, and false, before 2026-08-17.
if [ "${1:-}" = "--print-toolchain" ]; then
  printf 'bin=%s\nreal=%s\nsource=%s\nversion=%s\npin=%s\n' \
    "$lean" "$lean_real" "$lean_source" "$lean_version" "$pinned_toolchain"
  exit 0
fi

export AXEYUM_LEAN_BIN="$lean"
export AXEYUM_REQUIRE_LEAN=1
# Pass the deviation flag through explicitly, so a suite's own pin assertion
# agrees with the decision this gate already printed.
[ "${AXEYUM_LEAN_ALLOW_UNPINNED:-}" = "1" ] && export AXEYUM_LEAN_ALLOW_UNPINNED=1

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
  # WHICH Lean did this suite actually use? Exporting AXEYUM_LEAN_BIN is an
  # instruction, not evidence: a suite is free to resolve its own binary (and
  # `real_lean_wire_differential` deliberately does). Read the banner each suite
  # prints and require it to name the binary this gate resolved -- otherwise the
  # count above is a sum over runs against different checkers, which is exactly
  # the defect this policy exists to close.
  used_bins=$(sed -n 's/.*AXEYUM-LEAN-TOOLCHAIN [^ ]* bin=\(.*\) version=.*/\1/p' "$log" |
    LC_ALL=C sort -u)
  if [ -z "$used_bins" ]; then
    echo "check-lean-gate: $target reported $checked real-Lean check(s) but printed no" \
         "AXEYUM-LEAN-TOOLCHAIN banner, so which Lean produced them is unknown. A result that" \
         "does not name its checker is not evidence." >&2
    failed_suites+=("$target(unnamed-toolchain)")
    fail=1
  else
    while IFS= read -r used; do
      [ -n "$used" ] || continue
      # Compare resolved paths: one binary can be reached by two names through
      # elan's symlinks, and that is agreement, not a mismatch.
      used_real=$(readlink -f "$used" 2>/dev/null || printf '%s' "$used")
      if [ "$used_real" != "$lean_real" ]; then
        echo "check-lean-gate: TOOLCHAIN MISMATCH in $target -- this gate resolved $lean_real but" \
             "the suite ran $used_real (reported as $used). Two entry points checked different" \
             "things in one run; the totals below would have summed over both." >&2
        failed_suites+=("$target(toolchain-mismatch)")
        fail=1
      fi
    done <<<"$used_bins"
  fi
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
echo "check-lean-gate: OK -- $total_checked modules/controls were READ by $lean_version" \
     "($lean, via $lean_source; every suite confirmed the same binary)." \
     "$structural_families of $((theory_families + structural_families)) crosscheck families are" \
     "attestations, so this is not a count of propositions proved"
