# One framework instead of six tools — what actually happened in this run

Record of the pipeline as executed for `S(3; s,t,u)`, 2026-08-13. Not a
marketing page; the seams are in section 3.

## 1. Stage by stage

| stage | axeyum component | conventional toolchain | what happened here |
|---|---|---|---|
| model the problem | `ColouringFamily`, extended with `constraints_for_colour` / `colour_dependent` / `symmetry_blocks`; `ColouringProblem::per_colour` | a hand-rolled Python generator per problem | The family is ~200 lines: the equation enumerator, the independent verifier, and the block structure. Nothing downstream changed. |
| encode to CNF | `ColouringProblem::encode` | ad-hoc script, typically with no parity check against anything | One encoder for every family in the crate. I verified the uniform path was untouched by diffing 556,911 bytes of DIMACS from pristine `HEAD` against my tree over 29 Rado/Schur instances. A separate script has nothing to be diffed against. |
| reduce | `OffDiagonalSchur::minimal_solution_sets` | usually absent; or a separate preprocessor whose soundness argument lives in a comment | Subsumption-minimal antichain, in the same module as the enumerator that defines the sets, so "the retained list is a subset of the full list" is checkable in a unit test rather than asserted. `L(8)` on `[1,87]`: 2,576,807 → 75,433. |
| search | `axeyum_cnf::solve_with_drat_proof_streaming` (pure Rust CDCL) | kissat or cadical | 22 cells decided; every solve under 2.2 s. `min_conflicts` was also available in-crate and I measured it head to head — see FEEDBACK item 4. |
| proof production | streaming `TextProofSink` | a solver-specific `--proof` flag, binary format | Streamed to disk, so the proof's memory footprint is a fixed buffer regardless of instance size. |
| proof checking | `axeyum_cnf::check_drat_backward` | drat-trim | 22 refutations, 54–682 steps each, all re-derived. Same process, same data structures, no file-format round trip. |
| witness verification | `OffDiagonalSchur::first_violation` — a reachability search over the defining equation, sharing **no code** with the encoder | usually nothing; at best the encoder re-run against its own output | 23 of 23 lower-bound colourings replayed clean, then cross-checked a second time against the **full unreduced** solution-set list. |
| claim recording | `artifacts/claims/` ledger + `scripts/check-claim-certificates.py` | a sentence in a paper, artifacts on request | Each new value ships witness, deciding CNF, and DRAT with a machine-checked record. |

Both the deciding CNF and its refutation live in one process: the `bundle`
subcommand solves, checks its own proof, and refuses to write anything it could
not re-derive. There is no intermediate file whose provenance has to be argued.

## 2. The soundness trap, and why a fragmented stack could not have caught it

The stock encoder breaks colour symmetry: point 1 takes colour 1, and colour
class `i` may not begin before class `i-1`. That is sound **only because colour
names are interchangeable**, which is true for every family the crate had.

It is false for `S(3;s,t,u)`. Colour 1 forbids `L(s)`, colour 3 forbids `L(u)`;
they are different constraints and swapping them is not a symmetry. Imposing the
ordering deletes genuine colourings.

Concretely, measured: `S(3;3,4,5)` at `n = 41` **is** satisfiable — I have the
colouring and it is replayed by the independent enumerator. Encoded with
whole-palette symmetry breaking it comes back **`unsat`**.

Now trace that through a conventional pipeline. The bug is in the *generator
script*. The generator emits a CNF. kissat refutes it — correctly, that CNF
really is unsatisfiable. drat-trim verifies the refutation — correctly, the
proof really is valid. A referee re-runs both and gets the same answer. **Every
downstream tool reports success, and the published conclusion is a wrong `unsat`
that refutes an open conjecture.** Nothing in the chain has access to the fact
that the encoder's soundness precondition failed, because the precondition is a
property of the *modelling layer* and the chain begins after it.

What caught it here is that the modelling layer, the encoder, and the
independent verifier are one system with one notion of "violated":

* the symmetry precondition became a value — `symmetry_blocks()` — that the
  family must supply and the encoder consumes, so it is a thing a test can
  falsify rather than a sentence in a docstring;
* the *same* extension exposed a second latent copy of the violation predicate
  in `min_conflicts` (`search.rs:136`) that would have judged an off-diagonal
  colouring by the wrong rule. In a fragmented stack that closure would live in
  a different repository from the encoder and would never have been re-examined;
* the negative control is a committed test
  (`whole_palette_symmetry_breaking_produces_a_wrong_unsat`) that fails if
  anyone relaxes the restriction, because the encoder is reachable from the test
  suite. A generator script is not something a solver's test suite can regress.

A detail that makes the point sharper: I first tried four other off-diagonal
instances as the control and **all four agreed** under both encodings — the
over-strong constraint happened not to bite. Only `S(3;3,4,5)` at `n = 41`
exposed it. A fragmented stack does not merely lack the control; it gives no
reason to go looking for one.

## 3. Where the framework did not help

Honest seams, all of which are also in FEEDBACK.md:

* **The subsumption reduction started as a throwaway.** I wrote a standalone
  Rust program in a scratch directory to measure whether the antichain was worth
  computing, because there was no in-framework way to ask "how many clauses would
  this family emit at size `n`" without building the whole `Vec<Vec<usize>>`. The
  measurement that redirected the entire campaign happened outside axeyum.
* **The driver is outside the repository.** The decide/bundle loop — solve,
  decode, replay, write, check — is ~300 lines that every consumer re-invents;
  two existing examples in the crate contain variants of the same twenty lines,
  and my first version forgot to write the witness to a file at all, so 23
  lower-bound colourings existed only as stdout in a log until I extracted them.
  There is no `decide(family, n) -> Decision` in the crate where `Sat` *carries*
  the replayed witness.
* **Two colouring encoders exist** (`axeyum-cnf::colouring` and
  `axeyum-search::colouring`) and only one has a parity gate. The
  `axeyum-search` one's doc comment names a test file that did not exist. I had
  to establish encoding parity by hand.
* **The claim checker fails closed on a new family**, which is the right
  behaviour, but it means every new family needs an independent Python
  reimplementation of its semantics before anything can be recorded — real work,
  and a place where the "one framework" story stops and a second implementation
  in a second language begins. (That second implementation is also the point:
  it is the third derivation. But it is a cost, not a freebie.)
* **`CnfFormula` is a `Vec<CnfClause>` of `Vec<CnfLit>`.** 13.25M clauses cost
  2.3 GB of RSS for ~330 MB of literals. The framework's data structure, not the
  problem, sets the ceiling.

## 4. Cost of the extension, measured

Adding an entirely new *kind* of family — per-colour constraints, colours that
are not interchangeable — came to:

| piece | lines |
|---|---:|
| `offdiag.rs` (family: enumerator, subsumption reduction, independent verifier, blocks) | 914 incl. docs and unit tests |
| `colouring.rs` (per-colour constructor, block symmetry breaking, scoped violation) | +209 |
| `family.rs` (three defaulted trait methods, spec parsing) | +87 |
| `search.rs` (route the SLS through the shared predicate) | +27 |
| `tests/offdiag_schur.rs` | 277 |
| **everything else — encoder, CDCL, DRAT sink, backward checker, cube cover, ledger** | **0** |

The comparison is not "one file versus another". A bespoke route needs a
generator, a driver, a witness checker written independently of the generator
(or it checks nothing), a proof-checking step, and an argument that the four
agree — and it needs all of that *again* for the next family. Here the second
family costs the family.

The concrete return: the eleven published values were re-derived from both sides
in **119 seconds** on one host, which is what made it reasonable to treat them as
a gate on the encoder rather than as a separate validation exercise. Eleven new
values followed in the next twenty minutes.

## 5. Postscript: the reduction is why the frontier moved, and it is measurable

Added after an external novelty audit found that arXiv:2604.11030 has its own
computer-search table (Section 5, Table 3) covering five of the cells I had
labelled new. All five agree with our values, which turns our regression gate
from eleven published values into **sixteen**, five of them computed
independently in April 2026 by a different group with a conventional pipeline.

Their search stops at `(4,4,10)`, `(4,5,8)`, `(4,6,7)`, and their described
encoding has no subsumption reduction. Measured:

| cell | solution multisets | encoded clauses (minimal) | factor |
|---|---:|---:|---:|
| S(3;4,4,10) — their last | 46,281,800 | 239,130 | 194 |
| S(3;4,4,11) — new here | 176,224,094 | 323,293 | 545 |
| S(3;4,4,12) — new here | 633,107,771 | 451,622 | **1,402** |

Their frontier ends approximately where the *unreduced* encoding stops fitting.
Ours continues because the clauses that formed that wall were implied by clauses
we already had. This is a modelling-layer result — it lives in the family, above
the solver — and it is exactly the kind of thing that a stack split at the
CNF boundary has no place to put. A generator script emits clauses; it has no
notion of which of its own clauses are redundant, because redundancy is a
property of the relation, not of the file.

The corresponding honest note: the reduction is now so effective that
**enumeration, not solving, is the wall**. `S(3;4,4,12)` spends 164 s generating
633 million multisets to keep 451,622 clauses, which are refuted in 0.1 s. The
next frontier move is generating the antichain directly. Nothing in the
framework helps with that yet.
