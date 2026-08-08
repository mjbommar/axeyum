# Proof-Reconstruction Targets (Lean-horizon)

These are **targets, not benchmarks**. They state `∀`-theorems that genuinely
require **induction** — the kind of obligation axeyum's SMT engines return
`unknown` on, by design (see [../DEPTH.md](../DEPTH.md)). They are frozen here as
a fixed, honest set of goals to *check a proof against* rather than *decide*.
The in-tree Lean-core checker and bounded reconstruction routes now exist, but
these recursively defined induction theorems remain outside the reconstructed
slice. They align with [Software Foundations in
Lean](../foundational-books/proof-assistants.md).

**Important nuance:** over the *built-in* `+`, facts like `n + 0 = n` and
`a + b = b + a` are **Presburger-decidable** (LIA) — not Lean-horizon. The
genuine induction obligations are about **recursively-defined** operations (here,
`+` defined by recursion on a `Nat` datatype with `zero`/`succ`), whose universal
properties are *not* SMT-decidable. That is what these stubs encode.

## Files

- [`peano-add.smt2`](peano-add.smt2) — `Nat` as `zero`/`succ`, `add` by recursion,
  and the goal `∀n. add(n, zero) = n` plus `∀m n. add(m,n) = add(n,m)`. axeyum
  parses the datatype but returns `unknown` on the universals (induction needed).
- [`peano-add.lean`](peano-add.lean) — the same, as a Lean 4 sketch with the
  inductive `Nat`, recursive `add`, and the theorems stated (proofs `sorry`'d) —
  the reconstruction destination.

## Status

`lean-horizon` / not reconstructed. Do **not** wire the `sorry`-bearing sketches
as passing tests. Promotion requires a complete source-bound proof term, in-tree
kernel acceptance, the applicable external-Lean cross-check, and explicit axiom
audit; solver acceptance of finite instances is not enough.
