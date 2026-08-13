# Lean Nat order R4.1 result

Date: 2026-08-13

Status: **implemented locally; publication and hosted CI recorded separately**

Authority: [Lean kernel requirements](lean-kernel-requirements-2026-08-13.md),
R4.1; [ADR-0390](../research/09-decisions/adr-0390-proved-nat-strict-order-and-successor-inversion.md).

## Result

The shared zero-axiom Nat prelude can now state strict bounds with
`Nat.lt n m := Nat.le (Nat.succ n) m` and invert successor bounds through the
checked theorem
`Nat.le_of_succ_le_succ : Le (succ n) (succ m) -> Le n m`.

The inversion term is not a host-language shortcut. It constructs a
`Nat.rec` proposition family that is `False` at zero and `Le n x` at
`succ x`, then eliminates the indexed `Le` derivation with the kernel-generated
`Le.rec`. The step case composes `n <= succ n` with the carried bound through
the already checked `le_trans` theorem.

## Executable controls

The focused Nat suite checks five definitions and 25 theorems. It requires
`2 < 4` to reduce to `3 <= 4`, lifts and reinverts a proof of `1 <= 3`, and
requires a valid inversion proof to be rejected when assigned the false target
`4 <= 2`. The rejected name remains absent. Exact repeat builds remain
byte-stable and the environment still contains no axiom.

## Local validation

The implementation passed the following gates on 2026-08-13:

- `cargo test -p axeyum-lean-kernel`: 207 library tests, every integration
  suite, and the doctest passed; the focused Nat slice passed 8/8.
- `cargo test -p axeyum-solver --features full --lib`: all 1,121 solver library
  tests passed.
- strict `clippy` and warning-denied `rustdoc` passed for both the Lean kernel
  and full-feature solver surfaces.
- the axiom ledger remained fully classified at 65 assumptions and its eight
  mutation/unit controls passed.
- plan authority, documentation links, parity documentation, formatting, and
  diff-integrity checks passed; all 137 foundational concepts and 174 example
  packs validated with byte-stable generated dashboards.

These are local results. Publication and hosted CI are separate state and are
not implied by this section.

## Boundary and Rado consequence

This is a dependency-ordered R4.1 slice, not a complete order library.
Antisymmetry, totality, `min`, subtraction, cancellation, intervals, and finite
sums remain open. For the exact `thm:sharp` proof, this slice supplies the
meaning of strict range claims and the basic inversion step; it does not yet
prove the witness ranges or the reindexed geometric-sum identity.
