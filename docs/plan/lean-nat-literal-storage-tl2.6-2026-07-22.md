# TL2.6 result — arbitrary-precision Lean natural-literal storage

Date: 2026-07-22

Status: complete

Decision: [ADR-0346](../research/09-decisions/adr-0346-arbitrary-precision-lean-nat-literals.md)

## Result

TL2.6 removes the independent kernel's fixed-width natural-literal ceiling.
`Lit::Nat` now carries a canonical `NatLit` backed by
`num_bigint::BigUint`. Decimal parsing has no `u64` or `u128` intermediate;
equal values intern equally, distinct values remain distinct, and display
emits canonical base 10.

This is representation credit only. `Kernel::infer` still returns
`KernelError::UnsupportedLit`, no literal reduction is enabled, and the
official Nat dependency closure is not admitted. TL2.7 owns those semantics.

## Contract and implementation

- `NatLit::from_decimal` accepts only non-empty ASCII decimal digits.
- Leading zeroes are accepted and normalized by numeric value.
- Signs, whitespace, separators, non-ASCII digits, and empty strings reject.
- `Lit::nat` plus unsigned `From` implementations provide source-level
  conveniences without participating in wire parsing.
- Interning, cached structural metadata, lift, instantiate, universe
  substitution, hashing, equality, and both Lean render paths retain the full
  value.
- `axeyum-lean-import` validates format-3.1 `natVal` strings through
  `NatLit::from_decimal` and then declines with `literal-nat-typing`.
- The importer deliberately does not append the expression before TL2.7, so a
  parsed literal cannot acquire admission credit from boundary validation.

The dependency is unconditional because expression meaning cannot vary by
feature set. `num-bigint` is already used in the workspace, is pure Rust, and
does not change the no-C/C++ default or workspace `unsafe_code` policy.

The implementation plan's former dependency on TL1.7 declaration/axiom digests
was corrected to TL1.2. Digests authenticate completed environments; they do
not define expression-payload representation, and TL2.6 neither publishes an
environment nor admits a literal. TL1.7 remains queued before broader import
publication work.

## Boundary evidence

`nat_literal_bignum.rs` covers:

- `2^128 - 1` (`340282366920938463463374607431768211455`);
- `2^128` (`340282366920938463463374607431768211456`);
- `2^128 + 1` (`340282366920938463463374607431768211457`);
- a substantially larger decimal value;
- malformed spellings and canonical leading-zero behavior;
- exact interning, non-aliasing, structural preservation, Lean rendering, and
  the still-required `UnsupportedLit` inference result.

The deterministic TL2.15 seed expands from eight to ten literal corners with
explicit `2^128` and much-larger cases. Its total population remains 768:
256 literal/reduction cases plus the existing 512 Prop/universe/inductive
cases. Every attempted `False` admission still rejects, and the repeated
summary remains byte-for-byte deterministic in process.

The importer mutation family submits the three `2^128` boundary values and the
larger value directly as decimal strings. All four reach the stable
`literal-nat-typing` decline, while malformed strings and a JSON numeric payload
reject as format errors before that boundary. This distinguishes complete wire
representation from future typing.

## Validation

Passed locally:

- `cargo test -p axeyum-lean-kernel`: 179 unit tests and 29 integration cases
  across ten integration binaries; the separate doctest also passes;
- `cargo test -p axeyum-lean-import --tests`: 16 integration cases;
- warning-denied all-target Clippy for both crates;
- warning-denied rustdoc for both crates;
- focused rustfmt checks for every changed Rust source;
- generated Lean compatibility-contract validation and repository link checks.

The host's existing `/tmp` allocation was at its quota during the first
doctest link. Re-running with only rustc temporary files directed to `/dev/shm`
passed; no test limit, memory cap, or semantic configuration changed. The
repository-wide rustfmt gate remains separately red on pre-existing formatting
drift in unrelated crates and was not rewritten as part of TL2.6.

## What this does not claim

- no Nat literal has a kernel type yet;
- constructor-form and literal-form naturals are not definitionally equal yet;
- no Nat operation receives accelerated reduction;
- the official Nat, String, `Init`, `Std`, or mathlib closures are not admitted;
- arbitrary-precision storage does not by itself increase K1 compatibility
  credit.

## Next action

Execute TL2.7: type `Nat` literals, implement checked conversion between
literal and constructor forms, prove unary/literal definitional equality around
and above the old width boundary, and rerun the exact official Nat closure with
positive and rejecting mutations.
