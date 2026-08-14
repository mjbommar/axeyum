# Refactor and cleanup plan — August 2026

> **This is the engineering strand.** Its companion is
> [`docs/mathematics-2026-08/`](../mathematics-2026-08/README.md), which asks what
> mathematics the system can do rather than where the code is untidy. Read that
> one if you want the ceiling; this one is the floor.
>
> A third strand,
> [`docs/formalized-math-2026-08/`](../formalized-math-2026-08/README.md),
> covers collecting and integrating the ~10 M lines of formalized mathematics
> that already exist outside this project.
>
> **Before taking any item, read [`00-parallel-work.md`](00-parallel-work.md).**
> A second lane owns `crates/axeyum-lean-kernel/` and two shared append points,
> and it re-orders both strands.

A plan grounded in measurement, written after a twelve-hour multi-agent campaign
that pointed the whole stack at open mathematics and recorded where it bent.
Nothing here is an impression: every number was measured on 2026-08-14 and the
command that produced it is given.

This folder does **not** restate the architecture. Those documents exist and are
the input to this one:

- [`docs/internals/architecture.md`](../internals/architecture.md) — the layer diagram
- [`docs/research/03-architecture/system-architecture.md`](../research/03-architecture/system-architecture.md)
- [`docs/research/08-planning/foundational-dag.md`](../research/08-planning/foundational-dag.md) — the dependency *contract*, which says what must exist before a layer may depend on another

## The measured baseline

| fact | measurement |
|---|---|
| workspace size | **476,449** lines of Rust across 23 crates |
| `axeyum-solver` | **236,275 lines — 51% of the workspace**, 164 top-level modules, depends on 13 of 22 other crates |
| solver public API | **267 `pub use` re-exports** over 7 direct `pub` items — a façade, not a tangle |
| solver subsystems | quantifiers 38 modules · arithmetic 20 · arrays/BV 18 · UF 8 · strings 7 · dispatch 5 |
| tests | 278 integration files + 83 in-source `#[cfg(test)]` modules |
| library | `nat_prelude` **106 proved theorems, 0 axioms**; `int_prelude` **0 proved, 3 assumed**; `arith_prelude` **0 proved, 3 assumed** |
| library growth | `nat_prelude.rs` 3,856 → **9,969 lines in 60 commits**, one session |
| architecture doc | 82 lines, documents **11 of 23 crates**; omits `axeyum-cas` (47,472 lines, the second-largest crate) |
| decision records | **455 ADRs** |

## The four findings this plan is built on

**1. ℤ and ℝ are one hole running through every layer at once.** Five agents in
five crates hit it independently and each reported it as a local gap. It is not
five gaps. → [`01-int-real-keystone.md`](01-int-real-keystone.md)

**2. The components are adjacent, not composed.** Two real-algebra
implementations, two colouring encoders (one citing a parity test that does not
exist), and a Lean kernel rebuilt from scratch on every query at six call sites.
If the product is "an SMT solver, a CAS, and a proof-assistant kernel in one
process", then the *composition* is the product. →
[`02-composition.md`](02-composition.md)

**3. The god-crate is decomposable, and its seams are already visible.** 51% of
the workspace in one crate — but behind a 267-entry re-export façade, with six
clean subsystem groupings and a feature flag that already separates the minimal
deployment from the full one. →
[`03-solver-decomposition.md`](03-solver-decomposition.md)

**4. Gates report success over work they do not do, and documents assert what
the code does not.** Three gate-scope holes and one whole class of
prose-only guards were found in a single day — none by running the gates. →
[`04-gates-and-truth.md`](04-gates-and-truth.md)

## What this plan is not

It is not a rewrite. The measured evidence says the architecture is sound and
the *seams* are unfinished: a façade that is already a façade, subsystems that
already group cleanly, a dependency contract that already exists in
`foundational-dag.md`. Every item below is a matter of finishing a boundary that
is half-drawn, and each is independently landable.

Nor is it a performance plan. Where performance appears — the 4,000× kernel
rebuild, the 6.6× proof-checking blow-up since reduced to 1.5× — it appears
because it *bounds what can be proved at all*, not because it is slow.

## Order

The items are not equally urgent and they are not independent. **This is the
single-owner ordering; it is superseded while a second lane is live —
see [`00-parallel-work.md`](00-parallel-work.md), which is the operative
sequencing today.**

1. **`01` — ℤ/ℝ.** The keystone. Everything above it is currently assumed, and
   the layers cannot compose across a sort the evidence system cannot express.
   *Its first item, constructing ℤ from proved ℕ, is currently owned by another
   lane; the rest of `01` is free.*
2. **`02` — composition.** Directly blocks `01`: the CAS certificate is over ℝ
   while the mathematics is over ℤ, and the kernel rebuild tax rises with every
   theorem `01` adds. *W1 (kernel reuse) is contested; W2/W3 are free.*
3. **`04` — gates and truth.** Cheap, and it protects everything else. A
   refactor guarded by gates that do not see the files is not guarded. *Free.*
4. **`03` — decomposition.** The largest and the least urgent. Do it after the
   boundaries above are real, or it will freeze today's seams into crate
   boundaries. *Do not start while another lane is in `axeyum-solver`.*
