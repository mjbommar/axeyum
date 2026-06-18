# Depth & Scope: what this curriculum is (and is not)

This file states the honest ceiling of the curriculum so nobody mistakes the
**map** for the **territory**. Read it before assuming a `covered` node means
"taught to textbook depth."

## Two different things

1. **A curriculum map** — the [23-node prerequisite DAG](README.md). This is
   real and reasonably complete: the backbone is grounded in Lean Mathlib,
   Metamath, and bridge-course canon.
2. **A thin slice of decidable, self-checkable exercises** — ~50 small scenarios
   across ~10 families. `covered` means *"this node has ≥ 1 self-checking
   exercise,"* **not** *"taught to the depth of a textbook chapter."* Our entire
   number-theory node is a handful of exercises (Bézout, modular inverse, parity);
   a real number-theory text (Hardy & Wright; *The Queen of Mathematics*) is
   hundreds of pages.

## The decidability ceiling (why depth is bounded *in principle*)

axeyum self-checks two ways (ADR-0008): **UNSAT by exhaustive enumeration** over
a finite domain, or **SAT by evaluating a witness**. Both require a *finite or
computational* check. The deep content of analysis — Spivak's `∀ε ∃δ`, the
completeness of ℝ, "every continuous function on `[a,b]` attains its maximum" —
is **quantified over the reals and undecidable** for this machinery. So:

- The `calculus`, `reals`, `sequences-and-limits`, `complex`, and `cardinality`
  nodes are flagged **`lean-horizon`**: we can self-check their *algebraic
  shadow* (polynomial / real-closed-field facts), not their ε-δ heart.
- Reaching textbook analysis depth needs the **proof track** (the planned P3.6
  in-tree Lean kernel + P3.7 Alethe→Lean reconstruction) — where you *check a
  proof* rather than *decide an instance*. That is a different machine and does
  not exist yet.

## The honest scorecard (vs. canonical texts)

| Area | Canonical text | What axeyum covers |
|---|---|---|
| Calculus / real analysis | **Spivak**, *Calculus*; Rudin, *PMA* | The decidable shadow only: order axioms + transitivity (LRA, certified) and a monotonicity inequality (NRA). Even the degree-2 SOS inequality `a²+b²≥2ab` is the **NRA frontier** today, and the ε-δ chapters are `lean-horizon`. See [foundational-books/spivak.md](foundational-books/spivak.md). |
| Number theory | Hardy & Wright; *The Queen of Mathematics* | The computational core (gcd/Bézout, modular inverse, parity) — ~1% of the content, but genuinely decided and self-checked. |
| Abstract algebra | Dummit & Foote | Finite-instance axiom checks (group/ring/field over ℤ/2ʷ), not the structure theory. |
| Linear algebra | Axler, *LADR* | Fixed-size matrix identities + solving over BV/ℚ, not dimension/spectral theory. |

## What we genuinely got right

- The **map** and its prerequisite edges.
- **Decidability honesty**: every node states exactly how much axeyum can check
  and flags what it cannot (`decidable` / `computable` / `bounded` /
  `undecidable`; `covered` / `planned` / `lean-horizon`).
- A **working answer-key for the decidable exercises**, each oracle-free and
  re-checkable.

Think of the curriculum as a well-organized **table of contents with a verified
answer key for the decidable problems** — not the books themselves.

## See also

- [README.md](README.md) — the map and legends.
- [foundational-books/](foundational-books/README.md) — how specific texts
  (Spivak, …) project onto the decidability lens.
- [../research/08-planning/formal-mathematics-tour.md](../research/08-planning/formal-mathematics-tour.md)
  — the design rationale.
