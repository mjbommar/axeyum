# Proof-Reconstruction Targets (Lean-horizon)

These are **targets, not benchmarks**. They state `∀`-theorems that genuinely
require **induction** — the kind of obligation axeyum's SMT engines return
`unknown` on, by design (see [../DEPTH.md](../DEPTH.md)). They are frozen here so
that when the proof track lands (P3.6 in-tree Lean kernel, P3.7 Alethe→Lean
reconstruction), there is a fixed, honest set of goals to *check a proof against*
rather than *decide*. They align with [Software Foundations in
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

`lean-horizon` / not-yet-reachable. Do **not** wire these as passing tests; they
are documentation of where the proof track is headed. A future P3.7 milestone
turns each into a kernel-checked proof.
