# Lean Nat divisibility R4.3 result

Date: 2026-08-13

Status: **implemented locally; publication and hosted CI recorded separately**

Authority: [Lean kernel requirements](lean-kernel-requirements-2026-08-13.md),
R4.3; [ADR-0389](../research/09-decisions/adr-0389-proved-nat-divisibility-foundation.md).

## Result

The capability previously confined to `rado_shell_arithmetic` is shared Nat
prelude surface. `Nat.dvd a n` reduces to `Exists (fun q => n = a * q)`;
`Nat.dvd_mul` introduces the multiplication witness; and `Nat.dvd_add`
eliminates two witnesses and constructs their sum. All three declarations pass
the trusted kernel gate and add no axiom.

`NatPrelude` exposes stable handles for the definition and both theorems, and
`NatOps` exposes builders for the divisibility proposition and its witness
predicate. They participate in R1's exact-package snapshot, repeat, and
rollback contract.

## Executable controls

The focused Nat prelude suite now has eight tests. It checks four definitions
and 24 theorems, proves `2 | 6` and `2 | 10` through the public surface, and
requires the kernel to reject a valid `dvd_add` proof when relabelled as a
proof of `2 | (4 * 6 + 1)`. The rejected name is absent afterward. The axiom
walk remains empty and two independent builds render identically.

## Local validation

The implementation passed the following gates on 2026-08-13:

- `cargo test -p axeyum-lean-kernel`: 207 library tests plus every integration
  suite and doctest passed; the focused Nat prelude slice passed 8/8.
- `cargo test -p axeyum-solver --features full`: 1,121 library tests plus the
  full integration matrix and two doctests passed (only tests already marked
  ignored by the repository were skipped).
- strict `clippy` and warning-denied `rustdoc` passed for both
  `axeyum-lean-kernel` and the full-feature `axeyum-solver`.
- the axiom-ledger generator check reported 65 classified assumptions and
  zero unclassified entries; its eight mutation/unit controls passed.
- plan authority, documentation links, parity documentation, formatting, and
  diff-integrity checks passed; all 137 foundational concepts and 174 example
  packs validated and their generated dashboards remained byte-stable.

These are local results. Publication and hosted CI are separate state and are
not implied by this section.

## Boundary and next dependency

This is the witness foundation, not a completed number-theory library. It does
not add transitivity, cancellation, congruence, remainder, gcd, or valuation.
For `thm:sharp`, the next dependency should be selected from the exact proof
spine: the order/range lemmas and finite-sum empty-range/reindexing identity are
needed before the explicit witness can receive theorem credit.
