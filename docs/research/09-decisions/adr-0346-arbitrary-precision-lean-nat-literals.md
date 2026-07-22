# ADR-0346: Store Lean natural literals as canonical arbitrary-precision values

Status: accepted

Date: 2026-07-22

## Context

The independent Lean kernel represented `Lit::Nat` with `u128`. That ceiling
was inert while every literal failed closed at inference, but TL2.7 cannot type
or reduce literals soundly if TL2.6 leaves a narrower domain than Lean's
natural numbers. The pinned Lean 4.30 kernel stores literal naturals as `nat`
and exposes constructors from arbitrary-precision integers; official
`lean4export` format 3.1 serializes `natVal` as a decimal string.

The first official Nat dependency closure currently reaches one `natVal` at
line 125. Its old decline code combined two independent blockers:
`literal-nat-bignum-and-typing`. Representation must be completed and tested
without accidentally granting typing or declaration-admission credit.

## Decision

**Represent Lean natural-literal payloads with a public `NatLit` newtype over
the pure-Rust `num_bigint::BigUint`, and make `Lit::Nat` carry `NatLit`.
Canonical decimal parsing accepts exactly a non-empty sequence of ASCII digits
and never converts through a fixed-width integer. Keep literal inference and
reduction unsupported until TL2.7.**

The boundary contract is:

- equality, hashing, interning, and display operate on the numeric value;
- decimal input is canonicalized (`0001` and `1` denote the same value);
- negative signs, plus signs, whitespace, separators, non-ASCII digits, and
  empty input are malformed;
- the format-3.1 importer validates the complete decimal payload with
  `NatLit::from_decimal`, then declines with `literal-nat-typing` rather than
  constructing or admitting an expression;
- unsigned Rust values may enter through explicit `From` implementations or
  `Lit::nat`, but wire-format input never passes through those fixed-width
  conveniences;
- TL2.7 alone owns literal typing, constructor/literal conversion,
  definitional equality, and admission of the official Nat closure.

`num-bigint` is an unconditional dependency of `axeyum-lean-kernel`. It is
already present in the workspace, is implemented in Rust, and does not weaken
the default no-C/C++ or `unsafe_code` policies.

## Evidence and exit gates

TL2.6 is complete only when all of the following hold:

1. decimal values at `2^128 - 1`, `2^128`, `2^128 + 1`, and a substantially
   larger value round-trip canonically;
2. malformed decimal spellings reject deterministically;
3. interning distinguishes adjacent large values and coalesces equal values;
4. lift, instantiate, universe substitution, and Lean rendering preserve the
   exact value;
5. the seam-fuzz literal family contains values above `u128` while every
   attempted admission of `False` still rejects;
6. importer mutations at and above `2^128` reach `literal-nat-typing`, proving
   the wire path did not narrow, while malformed payloads reject before that
   boundary;
7. direct inference remains `KernelError::UnsupportedLit`.

Primary references:

- [Lean 4.30 kernel literal representation](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/kernel/expr.h)
- [`lean4export` 3.1 NDJSON format](https://github.com/leanprover/lean4export/blob/v4.30.0/format_ndjson.md)

## Alternatives

### Store canonical decimal strings

Rejected. It would make numeric equality and ordering depend on extra
canonicalization invariants at every use and would postpone the actual numeric
representation problem into TL2.7.

### Retain `u128` and decline overflow

Rejected. Lean naturals are not width-bounded, so this would turn a known
representation mismatch into a permanent compatibility exception.

### Feature-gate arbitrary precision

Rejected. Literal meaning is part of the kernel expression contract, not an
optional performance backend. Different feature sets must not assign different
representable domains to the same exported declaration.

### Implement storage and typing together

Rejected. The official fixture could then appear to close without separately
testing the no-narrowing representation boundary. TL2.6 and TL2.7 have distinct
failure modes and exit evidence.

## Consequences

- `Lit::Nat` is a deliberate public source-level API change.
- Natural literals allocate bignum storage even for small values; interning
  still canonicalizes repeated expression nodes.
- Import diagnostics now identify only the remaining typing blocker.
- Later Nat acceleration must consume the same exact value and provide its own
  checked-reduction evidence; this ADR grants no trusted arithmetic shortcut.
- ADR-0345's statement that the kernel had zero dependencies is historical at
  its acceptance point; the trust boundary remains independent and pure Rust,
  but now includes this narrowly scoped arithmetic representation dependency.
