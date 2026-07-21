# The existing corpus is a non-circular test harness for a CAS

Status: grounded analysis (2026-07-20)
Last updated: 2026-07-20

The claim that motivated this initiative: **axeyum already has the test harness /
correctness oracle for a CAS.** This note confirms it with the exact mechanism,
from a read-only survey of `crates/axeyum-scenarios/`, `docs/curriculum/`, and
`docs/rules-as-code/`.

## The oracle is self-grounded (non-circular)

`Scenario` (`crates/axeyum-scenarios/src/lib.rs:316`) bundles an arena, a query,
and an `expectation`. Ground truth is established by `Scenario::self_check`
(`lib.rs:349`) **without calling any solver** — the only trusted component is the
`axeyum_ir` term evaluator `eval`:

- **SAT scenarios** ship a witness the generator computed by *concrete execution*
  (e.g. `bezout_identity` runs extended-Euclid and installs `x,y`,
  `number_theory.rs:69`); `self_check` requires `eval(arena, term, witness) ==
  Bool(true)` for every constraint (`lib.rs:361`).
- **UNSAT scenarios** are the **negation of a theorem**; when total input width
  `≤ EXHAUSTIVE_BIT_LIMIT = 20` (`lib.rs:157`), `self_check` **enumerates all
  `1<<total_bits` assignments** and requires none is a model — a genuine
  finite-domain proof, returned as `UnsatEvidence::Exhaustive` (`lib.rs:386`).
  Above 20 bits it honestly downgrades to 4096 deterministic samples
  (`UnsatEvidence::Sampled`).

The in-code trust statement (`lib.rs:414`): *"a candidate answer is accepted only
because the evaluator (a small, trusted checker) confirms it satisfies the
original constraints — never because a search returned `sat`."* Tests
`catalog_scenarios_all_self_check` (`lib.rs:632`) and
`exhaustive_unsat_evidence_is_a_real_proof` (`lib.rs:672`) enforce it.

**This is exactly a CAS test harness's requirement**: a machine-checkable,
non-circular ground truth that can grade *any* engine's answer — including a CAS's
computed transform — because its own answers are certified by construction +
trusted exhaustive checking, not by trusting another CAS or solver. Existing CAS
test suites compare against *another CAS* (circular) or hand-computed keys
(trusted, not checked). This one does not.

## Coverage: a curriculum-organized map of the certifiable core

~165 concrete self-checking instances from 83 generator functions across 23
`Family` variants, mirrored onto a 23-node **decidability-tagged** curriculum DAG
(`docs/curriculum/curriculum.toml`; 19 `covered`, 4 `lean-horizon`):

- Logic / predicate / proof methods; BV identities & arithmetic (~33 base).
- Number theory & modular arithmetic (16); abstract algebra groups/rings/fields
  (10); polynomials (6); linear algebra (6).
- Number systems / induction / counting; sets & relations.
- Integers/reals/rationals/**real-algebra (RCF)** (Integer 7, Real 7, Rational 8,
  RealAlgebra 6) — the exact arithmetic destinations a CAS must respect.
- Software verification (6); memory QF_ABV (6); uninterpreted functions (18).

The curriculum nodes carry a `decidability` tag (`Decidable` / `Computable` /
`Bounded` / `Undecidable`), an `axeyum_theory`, and a `family` link. ADR-0033's
**"double-duty: teach = test"** thesis says these artifacts are one thing viewed
two ways; the CAS adds a **third** projection — the same certified identity is now
also a *regression test for a computed transform*.

## What it is not (the honest gap)

The corpus is **entirely verification-shaped**: every generator asserts/negates a
statement and decides it. A grep for compute/transform/simplify/differentiate/
solve-for functions returns nothing — there are **zero compute-shaped functions**.

So the harness is exactly that: a **harness**, not the engine. It gives the CAS
its checkable ground truth and its regression suite; it does not compute
derivatives, factor polynomials, or integrate. The initiative builds the compute
engine *against* this oracle — every new transform is validated by lowering its
correctness obligation onto (a) `self_check`-style exhaustive checking at small
width, (b) the exact `poly.rs`/`real_algebraic.rs` arithmetic, or (c) the
certified decision procedures. That is the whole point: **build the compute side
test-first against a correctness oracle that is already machine-checked.**

## Consequence for the plan

1. Every CAS transform ships a **self-checking scenario** in the same shape (the
   double-duty artifact contract, ADR-0033), so the corpus grows *with* the
   engine and the coverage audit (`coverage.rs`) keeps gaps visible.
2. The oracle's exhaustive-at-≤20-bits guarantee means the **certified polynomial
   kernel** (first slice) can be validated with genuine finite-domain proofs at
   small width, plus exact `poly.rs` agreement at all widths — no external CAS in
   the trust base.
3. The curriculum DAG is the **coverage/priority map** for which capabilities to
   build next (frontier = nodes whose prerequisites are covered).
