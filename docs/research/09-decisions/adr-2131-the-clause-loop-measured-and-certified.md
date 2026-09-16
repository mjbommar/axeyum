# ADR-2131: The clause loop, measured and certified — QF_NRA

Status: proposed
Index-summary: ADR-2126 built the Boolean clause loop for QF_NRA and shipped it
OFF and UNMEASURED, withholding its `unsat` because three obligations had no
checker — the Tseitin abstraction, every blocking clause, and the SAT core's
refutation. This builds that checker (`nra_clause_cert`) and the route now emits
`unsat` only when it accepts: each blocking clause KEEPS its `CellRefutation`
and is re-checked, the propositional half is a DRAT proof from a SECOND
independent solve checked by `check_drat`, and the abstraction is checked
structurally — the certificate carries the Tseitin GATE TABLE and not the
clauses, so the checker derives them itself after establishing that every gate
variable is fresh and that the table really describes the assertions. **But the
sizing corrects the premise twice and the second correction is the finding.**
Re-derived on the current binary the pinned draw is 124/200, not the board's
122; of the 76 undecided, 34 decline `non-conjunctive` — and only **16** are
inside the loop's shape, because 18 are over the 48-atom cap. `n_atoms` is
bimodal with that cap in an EMPTY GAP (55 files at 3..12, one at 103, then 62
from 125 up), so moving it anywhere from 13 to 102 changes nothing. No file in
the population uses `ite`, `=>`, `xor` or `distinct`. And what actually blocked
the work was neither: `check_cell_refutation` REJECTED `x > 1 ∧ x < 0` — reached
by the SHIPPED conjunctive route, not by anything new — through two false-reject
bugs in `has_root_strictly_inside`, both now fixed with regression tests beside
the checker. Neither z3 nor cvc5 checks a nonlinear lemma: z3's nlsat calls
`fail_if_proof_generation`, and cvc5's covering steps are `ProofRule::TRUST`
with a stub checker.
Index-status: proposed
Date: 2026-09-16

**Lane:** `nra-clause-loop`
**Supersedes in part:** [ADR-2126](adr-2126-exact-delineability-and-the-clause-loop-for-nra.md)
(`CadDecline::ClauseLoopUnsatUncertified`; the `CLAUSE_LOOP` arm's base)
**Artifacts:** [`bench-results/nra-clause-loop-20260916/`](../../../bench-results/nra-clause-loop-20260916/README.md)

## Context

[ADR-2121](adr-2121-single-cell-cad-for-nra.md) built the one-cell-per-conflict
CAD route and shipped its `sat` half. [ADR-2126](adr-2126-exact-delineability-and-the-clause-loop-for-nra.md)
made delineability exact, shipped the `unsat` half, and built the **clause
loop** — CDCL(T) over polynomial sign atoms with single-cell CAD as the
theory — behind its own lever, **OFF and unmeasured**, with its `unsat`
withheld. It named two things left undone: the loop's A/B, and the loop's
*certified* `unsat`. This ADR is both.

ADR-2126's withholding was stated precisely, and that is what made it
actionable. An `unsat` from the loop would rest on three things:

1. the Tseitin abstraction being equisatisfiable with the original query,
2. every blocking clause being implied over the reals,
3. the SAT core's refutation of the resulting clause set.

None had a checker. All three now do.

## Decision 1 — the sizing, before the code, and it halves the ceiling twice

Re-derived on the current `main` binary, one `--trace` pass per file through
`scripts/ledger-run-one.sh` (which keeps the whole stdout, so the verdict and
the decline cause come from the same run), s5 cores 1/9/3/11, 24 s, 8 GiB.

**The pinned 200-file QF_NRA draw is 124 decided (55 sat, 69 unsat), 76
undecided.** The 2026-09-15 board records 122 for this draw. A board TSV is a
snapshot, and a lane that sizes itself from one is sizing itself against a tree
that has moved.

Causes on the 76, and the one this lane cares about is the top row:

| files | cause |
|---:|---|
| **34** | **`non-conjunctive`** |
| 22 | `slice-bounds` |
| 6 | `algebraic-witness` |
| 4 | ABSENT — the watchdog killed the run before the rung |
| 3 | `coefficient-range` |
| 2 | `projection-resultant-zero` |
| 1 each | `declined/not-applicable`, `root-ordering`, `projection-arithmetic`, `projection-sylvester-dim`, `certificate-rejected` |
| **76** | **total** |

### The ceiling is 16, not 34

`non-conjunctive` says the conjunctive route refused the SHAPE. It does not say
the loop can take the file. Parsing the assertions of every such file (an
independent s-expression reader, `let` expanded under a 2,000,000-node budget
that never fired, so the counts are exact and not lower bounds):

| | the 34 undecided | all 118 `non-conjunctive` |
|---|---:|---:|
| `n_bool_vars > 0` — a Boolean leaf the loop cannot abstract | 1 | 46 |
| `n_atoms > 48` — over `MAX_CLAUSE_ATOMS` | 18 | 63 |
| **neither — admissible** | **16** | **55** |

Two denominator traps are visible in that table and both would inflate a
ceiling:

- The cause filter alone selects **118** files, but **84 of them are already
  DECIDED by a later rung** and can gain nothing. The ceiling is the
  intersection with "we do not decide it".
- Within the 34, the Bool-leaf decline predicts nothing the atom cap does not
  already predict: the single Bool-carrying file has 321 atoms and is over the
  cap anyway. Reporting 1 + 18 as 19 blockers would double-count.

### The atom cap is not a lever, and that is a measurement

`n_atoms` over the 118 is sharply bimodal: **fifty-five files at 3..12 atoms,
exactly one at 103, then sixty-two files from 125 to 63,180.** `MAX_CLAUSE_ATOMS`
is 48 and sits in the empty gap. **Moving it anywhere from 13 to 102 changes
nothing at all.** A lane briefed to "raise the cap" would have measured zero and
had no way to tell that from a cap that was already right.

### The connectives are not the work either

**Zero files in the population use `ite`, `=>`, `xor` or `distinct`**
(independently confirmed by grep), and `or` is binary in every file but one,
which reaches arity 4. The loop's handling of those connectives is correctness
surface, not reach. The 16 admissible files are also narrow in provenance — 10
are `meti-tarski` chunks and 3 are `Pine` — so the ceiling is small AND
concentrated.

## Decision 2 — the certificate

New module `crates/axeyum-solver/src/nra_clause_cert.rs`. `certify_unsat` emits
`Unsat` only when `check_clause_refutation` accepts. The three obligations are
discharged by three different kinds of evidence, and the split matters because
they are not equally hard.

### (2) The theory obligation — carried, then re-checked

Every blocking clause now KEEPS the `CellRefutation` whose covering closed it,
and the checker runs ADR-2126's `check_cell_refutation` on each, independently
of the producer having run it.

A blocking clause is over the atoms the covering **cited**, not over the whole
Boolean assignment. That is sound — a covering in which every cell is closed by
one of the cited atoms proves the cited atoms alone jointly unsatisfiable, and a
finer arrangement does not weaken a refutation — but "the producer only cited
these" is a claim. So the checker walks the whole covering tree and **rejects** a
lemma whose tree names an atom the clause omits
(`LemmaCellOutsideClause`). The certificate carries every distinction its
producer makes.

### (3) The propositional obligation — a second, independent solve

The loop searches with `IncrementalSat`. The proof comes from
`solve_with_drat_proof_within` — a **different solver**, run again on the derived
clause set — and is checked by `check_drat`. **The solver that found the
refutation does not also get to be the evidence for it.** If the two disagree —
the proof core returns `Sat` for a clause set the incremental solver called
unsat — the route decides nothing rather than believing either.

### (1) The abstraction obligation — the one with no off-the-shelf checker

The naive move is to re-encode the query in the checker and compare, which is
not a check but the producer run twice. Instead:

**The certificate does not carry the clause list at all.** It carries the *gate
table* — one `GateDef` per Tseitin gate variable, naming its connective and its
input literals — and the checker derives the clauses itself. There is nowhere
for a producer to put a clause. Three things are then established:

- **Freshness.** Every gate variable is defined exactly once and is distinct
  from every atom variable. That is what makes the gate definitions a
  *conservative extension*: a fresh variable constrained only by `g ↔ φ` cannot
  turn a satisfiable formula unsatisfiable. It is the entire soundness argument
  for (1), and it is three lines.
- **Faithfulness.** `check_encodes` walks the ORIGINAL assertion terms against
  the gate table: `not` flips polarity; `and`/`or`/`=>`/`xor` must be a gate of
  the matching kind whose inputs recursively denote the arguments; a leaf must be
  a polynomial comparison equal to the certificate's atom for that variable. The
  walk reads terms and table and never builds a clause.
- **Rooting.** The unit clauses are exactly the literals for the assertions, one
  per assertion, none missing and none extra.

`gate_clauses` — the map from one gate definition to its clauses — is shared
between producer and checker **on purpose**, because a second hand-written copy
would drift. It is pinned by `gate_clauses_are_exactly_the_connective`, which
enumerates every assignment over the gate and its inputs and requires the clause
set to be satisfied on exactly the rows where `g ↔ op(inputs)`, in BOTH
directions, plus a row count. An exhaustive semantic test on the shared function
is stronger evidence than a duplicate implementation.

### `ClauseLoopUnsatUncertified` is removed

It meant "the loop refuted the abstraction and no checker exists for that". That
sentence is false now. A cause no code can produce is worse than no cause: it
reads as a live limitation in every table that prints the enum.
`ClauseLoopCertificateRejected` replaces it and means something strictly
stronger — the checker exists, ran, and said no.

## Decision 3 — what actually blocked this was ADR-2126's checker

The first end-to-end run rejected every certificate. The cause was not the
clause loop.

`check_cell_refutation` **rejected `x > 1 ∧ x < 0`** — about as small as an
unsatisfiable conjunction gets — reached by `decide_single_cell`, the route
ADR-2126 SHIPPED, with nothing from this lane involved. Two bugs in
`has_root_strictly_inside`, both **false rejects**:

1. **A root of the closing atom sitting exactly ON the cell boundary.** The atom
   that closes a cell is usually one of the boundary polynomials, so the two
   share that root by construction; the sliver count at that endpoint then stays
   at 1 through every bisection and the check exhausts `REFINE_DEPTH`. It was
   handled for EXACT endpoints only — and bisection from the Cauchy bracket
   `(-3, 3)` never lands on the rational 1, so that endpoint is never marked
   exact. Fixed by deciding "does `q` vanish at this root" **exactly**, with
   `sign_at_root` using the endpoint's own polynomial and Sturm chain.
2. **An unbounded cell whose Cauchy bound does not clear its finite endpoint** —
   cell `(2, +∞)` with `q = x`, whose bound is exactly 2. The counting interval
   came out empty, and there is nothing on the infinite side to refine, so the
   loop could only spin. Fixed by pushing the infinite side past the finite one.

Both directions are safe, and the argument is the same shape for each: the fix
subtracts or widens over a region it has **proved** root-free. A root at a closed
endpoint does not break sign constancy on the OPEN cell, which is the property
the function is asked about; and every real root of `q` is strictly inside
`(-C, C)`, so counting over `(a, b]` with `b ≥ C` is counting over `(a, +∞)`.

The regression tests live **beside the checker, not beside the loop**, because it
was the checker's defect. Two go red on a revert of the corresponding fix, and a
third is a satisfiable-conjunction control so neither can be read as the checker
getting looser — without it, a "fix" that made `has_root_strictly_inside` always
answer "no root inside" would pass both.

This is the ADR-2126 `certificate-rejected` bucket, and it was 1 file of 24 in
that sizing. The bucket was an undercount of the class, not of the cause: on the
population that lane measured, only one file reached the checker at all.

## Decision 4 — the A/B arm was confounded and had to be rebased

`CadPolicy::CLAUSE_LOOP` was defined as `SINGLE_CELL_SAT + clause_loop`, which
was correct when ADR-2126 wrote it, because `SINGLE_CELL_SAT` was then the
default. **ADR-2126 also moved the default to `SINGLE_CELL`.** From that moment
an A/B of default-against-`clause-loop` differed in **two** fields —
`emit_unsat` as well as `clause_loop` — so the treatment arm would have had the
single-cell route's `unsat` half switched OFF, and every verdict that half
contributes would have read as a **loss caused by the loop**. A confounded A/B
that prints a clean number.

The arm now carries `emit_unsat: true` and differs from the shipped default in
exactly `clause_loop`. `the_single_cell_arm_differs_in_exactly_the_route` reads
the comparison arm out of `CAD_DEFAULT` rather than naming it, so repointing the
default without rebasing the arm fails the test.

## Decision 5 — what the references do, and do not, check

Both reference solvers run this shape. Neither checks the lemma.

| | shape | evidence for a nonlinear lemma |
|---|---|---|
| **z3** nlsat | CDCL over sign atoms: `search()` at `nlsat_solver.cpp:1848`, conflict to `resolve` at `:2639`, `resolve_lazy_justification` at `:2454` calling the single-cell explainer (`nlsat_explain.cpp:1567` `compute_conflict_explanation`, projection at `:1454`) at `:2469`, learned clause added at `:2766`/`:2792` | **none.** `nlsat_tactic.cpp:144` is a literal `fail_if_proof_generation("nlsat", g)`. The only validation is an optional debug-mode re-solve of the negated lemma with a 1-second timeout (`nlsat_solver.cpp:1160`), plus an assumption-based unsat core (`:2260`) which is not a proof |
| **cvc5** coverings | CDCAC inside theory combination: `cdcac.cpp:555` `getUnsatCoverImpl`, characterization at `:358`, exclusion interval at `:444`; lemma emitted at `coverings_solver.cpp:134` as `InferenceId::ARITH_NL_COVERING_CONFLICT` | **a proof tree with the right shape and no checked content.** Every covering step is `ProofRule::TRUST` tagged `TrustId::ARITH_NL_COVERING_DIRECT` / `_RECURSIVE` (`coverings/proof_generator.cpp:106`, `:139`); the only real rule used is `SCOPE`. `coverings/proof_checker.cpp:33` returns `Node::null()` unconditionally and `registerTo` registers nothing — the header says so |
| **ours** | the same loop, `nra_clause_loop.rs` | the covering per lemma re-checked by `check_cell_refutation`, the abstraction checked structurally against the terms, and a DRAT refutation from an independent solve checked by `check_drat` — and no `unsat` without all three |

This is an uncontested axis rather than a parity claim. Our *reach* on this
route is 16 files; theirs is the division. What is different is that a verdict
from here carries evidence a referee can re-run.

## Consequences

- The `clause-loop` arm's `unsat` is real and certificate-gated. A refused
  certificate is a decline, so the arm cannot widen what is answered without
  widening what is checked.
- Two false rejects are gone from the **shipped** conjunctive route, which is a
  gain this lane did not set out to make and did not measure separately from the
  loop until the A/B.
- `GOVERNED_FILES` gains the five NRA route files. ADR-2126 found it named
  `nra.rs` and nothing else from the route, so
  `every_governing_constant_is_registered` could never ask about the cell caps,
  the slice bounds, the refinement depths or the clause-loop budgets — every one
  of which declines a query when crossed.
- The clause loop's own decline causes are observable for the first time.
  `CAD_DECLINE` is sticky and is already full of `non-conjunctive` by the time
  the loop runs, so every one of the loop's causes was recorded into a slot that
  could not take it. `CLAUSE_DECLINE` is a second slot; the single-cell route's
  attribution is untouched.

## What this does not claim

- It does not claim the loop is worth shipping ON. That is the A/B's answer and
  it is recorded in the ship decision below, against a ceiling of 16 files.
- It does not claim the certificate is cheap. Two solves and a full re-check per
  refutation is more expensive than the verdict, and the A/B's timing columns
  are where that shows up.
- It does not claim `check_cell_refutation` is now free of false rejects. Two
  were found by walking into them; the population that would measure the rest is
  the `certificate-rejected` bucket, which is 1 file on the pinned draw.
