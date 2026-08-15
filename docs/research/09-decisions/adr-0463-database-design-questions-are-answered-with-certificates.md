# ADR-0463: Relational Database Design Enters The Stack As Certificates, Not Verdicts

Status: accepted
Index-summary: Schema-design questions are decided twice and reported only with a replayable certificate; the domain model lives in `axeyum-scenarios`, not a new crate
Date: 2026-08-15

## Context

The project's owner asked for the stack to be pointed at useful computations —
"planning, logistics, database design, or general numerical approximation".
Planning and logistics already had a foothold (schedule infeasibility, IIS
cores, Farkas certificates reconstructed into Lean). Database design had
nothing.

It is a good fit on the merits and not only because the gap existed. The core
questions of relational schema design are *decidable logical implication
problems with small certificates*:

| question | positive certificate | negative certificate |
|---|---|---|
| `F ⊨ X → Y` | Armstrong derivation (reflexivity / augmentation / transitivity) | two-row relation satisfying `F`, violating `X → Y` |
| `X` is a candidate key | derivation of `X → R`, plus one removal test per attribute | two-row relation whose rows agree on `X` |
| schema is in BCNF / 3NF | one derivation per dependency of `F` | the violating dependency plus its two-row relation |
| decomposition is lossless | chase trace ending in an all-distinguished row | the final tableau read as a relation, with a spurious tuple |
| `Q₁ ⊆ Q₂` | homomorphism `Q₂ → freeze(Q₁)` (Chandra–Merlin) | `freeze(Q₁)` as a counterexample database |

The last row is the sharpest statement of this project's identity sentence
anyone has found: finding the homomorphism is NP-complete, and checking it is a
nested loop over the atoms of one query.

Two things had to be decided before any of it could become public surface.

## Decision

**Every database-design question is decided at least twice, by routes that
share no code, and no verdict is reported without a certificate that an
independent checker has already replayed.**

Concretely, and in the order the trust flows:

1. **The finder is untrusted.** Attribute closure, the tableau chase and the
   backtracking homomorphism search all produce certificates rather than
   answers. Nothing downstream consumes their verdict directly.
2. **The checker knows less than the finder, deliberately.**
   `check_derivation` implements the three Armstrong axioms and the citation of
   a dependency of `F` — and nothing else. No union rule, no decomposition
   rule, no pseudo-transitivity, and above all no attribute closure. A
   derivation needing a derived rule must spell it out in the three axioms,
   which is exactly what makes the certificate checkable by someone who does
   not have our code. `check_two_tuple_witness` compares bits.
   `check_chase_trace` replays identifications onto a freshly built tableau.
   `check_homomorphism` applies a map and looks things up.
3. **The solver is a second decision procedure, not the trust base.**
   A dependency set is a Horn theory, and homomorphism existence is a one-hot
   Boolean encoding, so both go through the real stack — bit-blast, CNF, SAT.
   The routes must agree; a disagreement is a reported FAILURE, never a
   tie-break. And when the solver says `sat`, **its model is the certificate**:
   the set of attributes it makes true is the agreement set of a two-row
   counterexample relation, which is then evaluated against `F` row by row.
4. **The instance pins its own answers.** A `.dbd` / `.cq` file carries
   `expect …` lines; a file that pins nothing is REFUSED, and a run that
   executes fewer expectations than the file declares fails. This is the
   direct answer to the 2026-08-15 audit finding that 40 of 162 checker runs in
   the fact ledger exited 0 on *completion alone*.
5. **The checkers are measured to fail closed.**
   `scripts/check-dbdesign-negative-controls.sh` runs 13 committed instances
   that each pin exactly one FALSE answer and requires a non-zero exit from
   every one, plus assertions that a wrong `--expect-checks` count, an instance
   fed to the wrong checker, and a `--verify-formal` script whose negation is
   satisfiable are all rejected — and that the true instances are still
   accepted, without which a checker that rejected everything would pass.

**The second decision: no new crate.** ADR-0001 admits crates only after a
boundary is proven by use. The domain model lives in
`crates/axeyum-scenarios/src/dbdesign/`, whose charter — "self-checking,
oracle-free consumer workloads (SAT by concrete execution, UNSAT by
bounded-verified identities)", ADR-0008 — is what this is, in relational
clothing. It depends only on `axeyum-ir`, so it can build the solver queries
without pulling the solver in; the two driver examples live in `axeyum-bench`,
which already depends on both.

## Consequences

**A minimality claim here is absolute, and for a stronger reason than usual.**
[ADR-0455](adr-0455-minimality-is-relative-to-decidedness.md) requires a
minimality claim to record whether every removal test was decided; attribute
closure is a total function on a finite lattice, so they always are, and
`KeyAnalysis` reports the count rather than leaving it assumed.
[ADR-0460](adr-0460-a-decided-subset-test-may-still-be-a-test-of-the-route.md)'s
sharper failure — a decided test that is really a test of the producer's
decomposition — is structurally absent: closure is defined by `F` alone, with
no monomial order, no block decomposition, no budget and no heuristic anywhere
in it. The independent evidence makes this concrete, because the evidence for
each negative verdict is not the closure computation but a two-row relation,
which refutes superkey-hood without mentioning closure at all.

**The negative direction often rests on less than the positive one**, which is
the reverse of the usual asymmetry and is recorded in each fact's
`axiom_footprint` rather than smoothed over:

- *Lossy* needs no theorem — a relation satisfying `F` whose projections rejoin
  to a tuple it does not contain is a complete refutation. *Lossless* needs the
  soundness of the chase (Aho, Beeri and Ullman 1979).
- *Not contained* needs no theorem — a finite database on which the two queries
  return different answer sets refutes the containment directly. In particular
  it never invokes Chandra–Merlin's converse, which requires an **infinite**
  domain (AHV Exercise 6.12a). Only the sound half is load-bearing.
- *Not implied* needs no theorem — and specifically not the COMPLETENESS half
  of Armstrong's theorem, which guarantees such a relation exists. Here one is
  exhibited, so the guarantee is not needed.

**One assumption is new to this ledger and easy to leave implicit**: every
attribute domain must have at least two values, or a two-row counterexample is
not constructible. It is in the footprint of every fact that uses one.

**`formal.statement` becomes checkable where the fact is propositional.**
`db_design_certify --verify-formal <file.smt2>` dispatches a committed script
asserting the NEGATION of a fact's recorded formal statement and requires
`unsat`. `F:orders-fd-implication-certified` uses it, so the proposition in the
ledger is machine-checked rather than transcribed. Its own negative control
(`negative-controls/wrong-formal.smt2`, satisfiable) is in the sweep.

**Scope this does not claim.** Only functional dependencies and conjunctive
queries. Inclusion dependencies are deliberately absent: implication for FDs and
INDs together is *undecidable* — proved independently by Chandra and Vardi
(SIAM J. Comput. 14(3):671–677, 1985) and Mitchell (Information and Control
56:154–173, 1983) — and a domain module that quietly answered such a question
would be answering a different one. A future extension must name its decidable
fragment (unary INDs with FDs is in polynomial time, Cosmadakis, Kanellakis and
Vardi, J. ACM 37:15–46, 1990) before it becomes public surface.

**Where the exhaustive sweeps stop is an error, not a smaller answer.** "These
are all the candidate keys" is refused above arity 24; the projected dependency
set is refused above fragment arity 16 (a truncated projection would be
*smaller* than the truth, turning a preservation question into a wrong `no`);
and a homomorphism search space above 50 000 000 maps is an error rather than a
silent `no`. An unsearched space and an exhausted one are the same output
otherwise.

## Evidence

- `crates/axeyum-scenarios/src/dbdesign/` — 37 unit tests, including one
  "tampered certificate is rejected" test per certificate family.
- `crates/axeyum-bench/examples/db_design_certify.rs`,
  `crates/axeyum-bench/examples/cq_containment_certify.rs`.
- `artifacts/instances/dbdesign/` — three positive instances (28 pinned
  expectations), one formal-statement script, 13 negative controls.
- `scripts/check-dbdesign-negative-controls.sh` — 22 assertions, 2.1 s warm.
- Facts `F:orders-fd-implication-certified`,
  `F:orders-candidate-keys-and-normal-forms`,
  `F:bcnf-decomposition-lossless-not-dependency-preserving`,
  `F:conjunctive-query-containment-homomorphism-certified`.
