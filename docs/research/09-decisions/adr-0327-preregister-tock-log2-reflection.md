# ADR-0327: Preregister Tock log2 reflection prerequisite

Status: accepted
Date: 2026-07-21

## Context

ADR-0326 closes the selected Maestro build route before LLVM emission because
the owning build requires an unregistered network font input. P5.5 still needs
an authenticated external target, while the reviewer-aligned plan forbids
turning a build failure into relaxed provenance or another curated fixture.

The replacement selection audit chooses two public Tock kernel integer-log
helpers at revision `ac5d597d22fbf3b03ef2169a577bac246ef65ffb`.
They are used by real MPU, ADC, and watchdog code and compile in the owning
release `kernel` library to single-block scalar LLVM. The current frontend
declines their LLVM 22 call-result `range` attribute before reaching the also-
unsupported `llvm.ctlz` intrinsic. Both forms have poison semantics and cannot
be erased.

## Decision

Add one bounded checked-reflection prerequisite before any official Tock
capture:

- a typed optional non-wrapping integer result range on scalar calls; and
- a distinct scalar count-leading-zeros instruction with an explicit constant
  `is_zero_poison` flag.

Lower both through existing Bool/BV terms. This ADR adds no `axeyum-ir`
operator and no solver special case.

For a call-result range `[lo, hi)`, the reflected value remains unchanged and
its definedness is conjoined with `lo <= value < hi`. The first slice rejects
wrapped, empty, type-mismatched, vector, or multiple result ranges rather than
guessing. For `ctlz`, the reflected value is the exact count of leading zero
bits in the source width. Operand poison propagates. If `is_zero_poison=true`,
zero additionally makes the result undefined; if false, zero returns the
source width. Any result-range constraint is then applied to the computed
value.

This matches the official LLVM contracts: an out-of-range return is converted
to poison, and `llvm.ctlz(x, true)` is poison exactly when `x=0`.

## Frozen acceptance gates

1. Commit this zero-result ADR and the replacement selection note before
   changing checked syntax, reflection, canonical rendering, fixtures, or the
   external capture producer.
2. Preserve every existing typed instruction and all 81 standing semantic
   variants. No existing unsupported input may become silently accepted.
3. Represent the range as typed width/lower/upper constants. Accept only one
   non-wrapping, nonempty scalar integer range whose width equals the call
   result. Reject malformed punctuation, negative/out-of-width constants,
   `lo >= hi`, duplicate ranges, and range on unsupported calls with stable
   spans/error kinds.
4. Represent `ctlz` separately from two-argument same-width `umin`/`umax`.
   Require exact `llvm.ctlz.iN`, a width-matched first argument, and a literal
   `i1 true` or `i1 false` second argument. Reject vectors, name/signature
   mismatch, nonconstant flags, extra attributes, `cttz`, and `ctpop`.
5. Compute the value from existing BV operations with deterministic structure.
   Define the zero behavior and range predicate explicitly; never constrain the
   value by assuming a range while omitting its poison/definedness effect.
6. Canonical render/parse/render is byte-stable and retains the exact range,
   tail marker, intrinsic name, widths, flag, and operands.
7. Unit tests cover parser/render success and every rejection above. Exhaustive
   widths 1--8 compare value and definedness against an independent native
   leading-zero oracle for both poison flags and accepted ranges. Deterministic
   32/64-bit rows include zero, powers of two, adjacent values, all-ones, and
   seeded values.
8. Proof tests establish the independent staged-bit-search specification for
   32 and 64 bits, plus zero and high-bit boundary properties. SAT mutations
   to zero handling, index constants, range bounds, and one high-bit partition
   must replay.
9. Extend `reflection_semantics_gate` manifest ownership and its exact counts;
   run complete `axeyum-verify` tests, strict Clippy/rustdoc, formatting,
   foundational resources, links, and the one-job 4 GiB OOM audit.
10. Do not commit Tock source or LLVM in this prerequisite. The non-crediting
    local feasibility module supplies no expected capture hash, symbol, parser
    result, proof, timing, or scoreboard value.
11. Acceptance permits only a new zero-row Tock capture ADR with two stable
    virtual roots, validated cache, offline raw-module equality, LLVM-22 tools,
    exact extraction/admission, atomic local output, and explicit attribution.
    It does not itself authorize external capture or solving.

No gate may be weakened after the first implementation test observes a Tock-
shaped fixture.

## Result

Accepted. The typed LLVM boundary now retains one non-wrapping result range and
a distinct `CountLeadingZeros` instruction, including the exact `tail` marker,
intrinsic name/signature, widths, operand, and literal zero-poison flag.
Malformed, negative, out-of-width, wrapped, empty, duplicated, mismatched, or
unsupported forms fail with located stable parser classes. Ordinary direct
calls remain outside this range profile.

Checked lowering constructs the exact count from existing extraction,
equality, and ITE terms. Operand poison propagates; zero poison and the
half-open result range affect definedness rather than constraining the value.
The selected-arm definedness rule proves the Tock-shaped zero guard does not
eagerly observe the poison-producing `ctlz(0, true)` arm. Existing `umin` and
`umax` calls receive the same range-definedness rule.

The accepted evidence includes:

- exhaustive native-oracle agreement for widths 1--8 across both poison flags
  and full/restrictive accepted ranges;
- deterministic 32/64-bit zero, power-of-two, adjacent, all-ones, and 128
  seeded rows;
- solver proofs that the 32/64-bit values equal an independently built
  threshold-partition specification and that the guarded Tock-shaped function
  is universally defined; and
- replayed countermodels for wrong zero handling, one count constant, the
  admitted range bound, and the high-bit partition.

The standing semantics inventory passes at 82 variants / 18 groups / 12 test
binaries / 129 tests. The checker owns 34 proof tests, 26 fuzz/replay tests,
and 18 refutation tests. Complete all-feature `axeyum-verify` tests/doctests,
strict package Clippy/rustdoc, the registered gate and its ten checker
mutations, foundational resources, documentation links, and targeted rustfmt
pass in the one-job 4 GiB scope. Workspace-wide `cargo fmt --all --check`
remains pre-existing red only on clean `axeyum-cas` sources outside this ADR;
no such file is included here. No external Tock byte, capture result, target
proof, or scoreboard row exists. Acceptance authorizes only a new zero-row
capture ADR with the roots/cache/offline/LLVM-22/atomic-output conditions in
gate 11.

## Rejected alternatives

- **Ignore `range`.** Rejected: LLVM converts out-of-range returns to poison.
- **Treat zero as always defined.** Rejected: `is_zero_poison=true` is explicit
  in both selected definitions.
- **Desugar the extracted text.** Rejected: it would authenticate Axeyum's
  rewrite rather than the external compiler output.
- **Add a public IR `bvclz` operator first.** Rejected: existing BV terms can
  express the bounded reflection semantics, avoiding an unmeasured solver and
  lowering surface.
- **Capture before semantics.** Rejected: an authenticated corpus that the
  strict parser cannot admit does not advance T5.5.

## Consequences

- The external target creates a small, source-backed frontend demand rather
  than a speculative operator expansion.
- Poison and range handling strengthen the correctness contribution and keep
  the eventual Tock proof independent of permissive LLVM-text normalization.

## References

- [Tock replacement selection](../../plan/track-5-verified-systems/P5.5-target-selection-tock-log2.md).
- [P5.5 external target](../../plan/track-5-verified-systems/P5.5-external-target.md).
- [LLVM `range` attribute](https://llvm.org/docs/LangRef.html#range-attribute).
- [LLVM `ctlz` intrinsic](https://llvm.org/docs/LangRef.html#llvm-ctlz-intrinsic).
- ADR-0281, ADR-0284, ADR-0290, and ADR-0326.
