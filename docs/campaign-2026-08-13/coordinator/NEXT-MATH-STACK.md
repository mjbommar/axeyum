# The next improvements to axeyum's mathematical stack

Five, ordered. Each is grounded in something measured during the 2026-08-13
campaign, and each names the experience that motivates it. CAS / library /
proof assistant / solver / kernel — not infrastructure.

---

## 1. Streaming resolution reconstruction — kernel + proof assistant

**The measurement.** `crates/axeyum-solver/src/reconstruct/resolution.rs`
reconstructs a propositional-resolution proof into a Lean proof term of type
`False` that our kernel type-checks. It is the real thing and it is the
clausal-layer foundation shared by QF_BV and SAT. But it **inlines**, and fails
with *"Davis–Putnam working set exceeded `DP_POOL_BUDGET` clauses (proof too
large for inlined resolution reconstruction)"*.

**Why it is first.** Today Lean's own kernel accepted an axeyum development for
the first time — but only the shell *arithmetic*. The load-bearing half, the
**refutation**, is Lean-certified only at toy scale. `R_4(5(x-y)=4z) = 741` has
**699,572,027 proof steps**.

The competitive read is precise rather than rhetorical: AB Support LLC
(Zenodo, 2026-06-18) claim a Lean certificate of "the unsatisfiability of the
threshold instance" — for `R_4(x+y+z=2w) = 19`, where `n = 19` and inlining is
trivial. **We have that capability at that scale too.** Nobody has shown it at
a scale where the mathematics is open. That is the gap worth owning.

**Do:** lift the reconstruction from an inlined pool to a streamed one, so proof
size is bounded by disk rather than by an in-process working set. Coordinate
with the `axeyum-cnf` file-backed checking work — it is the same underlying
constraint (every trusted-path component currently assumes the artifact fits in
RAM) and the same techniques apply.

---

## 2. Wire the CAS into the solver — CAS + solver

**The measurement.** `axeyum-cas` is 46,854 lines and **465 public functions** —
`groebner.rs`, `sturm.rs`, `algebraic.rs`, `interval_arith.rs`, `mvpoly.rs`,
`ntheory*.rs`, `series.rs`, `orthopoly.rs`, `ratint.rs`, `gosper.rs`. The
solver's entire use of it is **two touchpoints**: `ntheory::gcd` and `MvPoly`.
ADR-0386 gave the CAS its first dependent on 2026-08-12 — one day before this
campaign.

**Why it matters, from this experience.** The `forall`-route proved the `k = 2`
Rado case for **symbolic `a` and `b`** over unbounded ℤ — a theorem, not a table
row. It then stalled at `k = 3`, needing *degree-3/4 inequalities in three
variables*. That is precisely real-algebraic decision work: Sturm sequences,
Gröbner bases, positivity certificates, interval arithmetic. **We own all four
and the solver cannot call them.**

This is also the honest answer to "did you find real mathematics?" Today
produced 18 confirmed table entries and one refuted prediction. A discharged
symbolic-parameter theorem would be an infinite family — a different kind of
result, and the one the stack is uniquely shaped to produce.

**Do:** a real bridge from the NIA/NRA/quantified routes into `axeyum-cas`
real-algebraic machinery, with the certificate discipline the rest of the
project has — a CAS answer that cannot be re-checked is not evidence.

---

## 3. Build `Int` on proved `Nat` — the library track

**The measurement.** `nat_prelude.rs`: **57 kernel-proved theorems, 0 axioms**,
and the content is the real API — `add_comm`, `add_assoc`, `add_left_cancel`,
`add_le_add_left`, `le_antisymm`, `div_mod_exists`, `div_mod_unique`, `dvd_add`,
`dvd_mul`. `int_prelude.rs`: **0 proved**, and its content is equally
Mathlib-shaped and entirely assumed — `add_assoc`, `add_comm`, `left_distrib`,
`le_total`, `le_trans`, `lt_of_le_of_ne`, `lt_irrefl`, `euclidean_decomposition`,
`eq_em`. PLAN.md's R2 decision records **34 Int assumptions retained**
(re-count this; my file-level greps have undercounted helper-built declarations
twice today).

**Why now.** This is the Mathlib-replacement track and it has a clean, countable
objective: **discharge Int assumptions against proved Nat.** Every one moved
from `Axiom` to `Theorem` shrinks the trusted base of everything above it,
including the Rado work, which R2 already routes through Nat prefixes for
exactly this reason.

**Metric to publish:** assumptions remaining, per prelude, per release. That is
a number a referee can check and a competitor cannot fake.

---

## 4. Automatic lemma splitting and hypothesis minimisation — solver

**The measurement (2026-08-12, in the register as B4).** **Every** monolithic
query carrying a full hypothesis set returned `unknown` — 8 of 8. The same
content split into 3–4-hypothesis lemmas closed in **0.00 s**. Minimal
hypotheses beat a bigger budget, decisively.

That decomposition was human work: four attempts and roughly 32 minutes of
solver time to find a split the tool would accept.

**Why it belongs here.** It is the difference between a tool an expert can coax
and a tool that works — and it is the direct enabler of item 2, because the
symbolic route's failures are exactly the monolithic-query shape.

---

## 5. The misconception corpus as a negative-control evaluation — curriculum

**The measurement.** `../math-education/graph` carries **148 misconceptions**
alongside 1,566 concepts, and axeyum's curriculum is 23 nodes with decidability
classes wired to executing `axeyum-scenarios` families. The findings register
flagged the corpus as untapped (F5).

**Why this campaign makes the case.** Today the generator of claims — an agent,
repeatedly — produced confident, plausible, wrong statements, and every one was
caught by mechanical re-derivation rather than by care. A curated corpus of
**plausible-but-wrong mathematics** is precisely the evaluation set for whether
the stack detects that class, and we already own one.

**Do:** wire the 148 misconceptions in as a negative-control suite — each should
be refuted, or explicitly classified as out of the decidable fragment. A suite
where the expected verdict is *wrong* is the one that cannot pass vacuously.

---

## Not on this list, deliberately

More Rado numbers, more Schur values, `w(2;3,20)`. The marginal value of a
nineteenth confirmed table entry is below every item above.
