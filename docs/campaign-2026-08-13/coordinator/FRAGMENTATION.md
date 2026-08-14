# What axeyum united today, and where the seams still are

Campaign-level record for 2026-08-13. Per-agent detail is in each agent's own
`FRAGMENTATION.md`. This file is the aggregate, and it is written to be checked
against the diaries rather than believed.

The claim under test is not "axeyum is fast". It is that **a process normally
split across five or six independently authored tools runs as one system**, and
that the integration buys something a pipeline of good tools cannot.

## The conventional pipeline, for this exact class of problem

Establishing a Ramsey-type threshold `R` is, in the literature, six tools and
four file formats:

| stage | what people normally use |
|---|---|
| model the problem | a bespoke Python/C generator, per paper |
| encode to CNF | the same script, usually with no parity check |
| split the search | `march_cu` (cube-and-conquer), a separate binary |
| solve | kissat / cadical / lingeling |
| produce a proof | solver-specific DRAT flag, format varies |
| check the proof | `drat-trim`, a different program by different authors |
| verify the witness | often nothing; sometimes the encoder re-run against itself |
| record the claim | a table in a paper |
| formal certification | Lean/Coq, a separate world, typically years later if ever |

Two joints in that chain carry almost all the risk, and neither is checked by
any tool in it: **is the encoder faithful to the mathematics**, and **is the set
of cubes actually a cover**. Every downstream tool will happily certify a
perfectly valid UNSAT proof of the *wrong formula*.

## What we exercised today

### 1. A modelling change propagated through the whole stack — and caught a wrong-UNSAT

agent-a extended the modelling layer for off-diagonal families (colours that
forbid *different* equations). That is not a new encoding option; it invalidates
an optimization three layers away: the stock symmetry breaking orders colour
classes by least element, sound only because colour names are interchangeable.
For `S(3;s,t,u)` with `s`, `t`, `u` not all equal they are not, and the stock
encoder would have produced a **wrong UNSAT** — a fake "conjecture refuted"
that kissat, drat-trim and every checker downstream would have confirmed,
because the proof would have been a valid proof of a formula that was not the
problem.

It was caught because the family definition, the encoder, the symmetry
breaking, the local-search predicate and the independent verifier are one
system with one notion of "violated". agent-a found it while extending the
trait; the coordinator raised the same trap independently from the diff. In a
fragmented stack there is no moment at which anyone is forced to notice.

The residue is instructive too: `search.rs`'s `min_conflicts` had its own local
copy of "all members share a colour", which would have silently ignored the new
per-colour scope. Integration does not mean the duplication cannot happen — it
means there is a single place where fixing it fixes everything downstream.

### 2. The search strategy and the certification obligation changed together

agent-b generalized cube-and-conquer from a flat product of branch choices to
an **adaptive trie**, so that cells exhausting their conflict budget get split
further instead of the budget being raised globally. In the conventional
pipeline, cubing (`march_cu`) and checking (`drat-trim`) are different programs
and "do these cubes actually cover the space?" is an assumption living in a
shell script.

Here, cover obligation 3 generalized from *exactly the flat product* to
*exactly the leaf set of a complete branch trie* in the same change, with four
failing-closed negative controls, including a hole inside a split branch and a
cube strictly contained in another. The obligation moved with the strategy
because they are the same program.

Second-order effect worth more than the first: cube codes were made
**shape-independent**, so a resumed run's ledger concatenates with its
predecessor's and certifies as one cover; and ledger rows are written only for
refuted cubes, so a cube abandoned by run 1 and refuted by run 2 does not
appear twice and trip the duplicate detector. That detector exists because a
contaminated artifact happened here before (1093 rows, 69 duplicates). A real
detector firing on a false positive during a resume is exactly how a real
detector gets disabled.

### 3. Untrusted search, trusted checking, two engines, one verdict

agent-c's refutation of the `a^k` law is the cleanest end-to-end instance. One
target ran: construction (written down from a lemma, not searched) → encode →
two independent searchers → proof production → checking → four-way witness
verification → claim ledger. The cover harness found the satisfying cube in
35.8 s; the batsat adapter independently found a **different** satisfying
assignment at 457.8 s; both were verified against the original formula by code
that shares nothing with the searcher.

The property that makes it believable on the first run: agent-c's warm-up
replication of `R_4(3,1) = 81` reproduced the stored claim's certificate step
count **exactly** — 164,538. Ledger, solver and checker agreeing bit-for-bit
across sessions and machines is an integration property, not a solver property.

And the eight lower bounds for eight parameter points cost **~0.5 s in total**,
because the construction came from Lemma 4.1 and was then checked three ways
inside the same framework. The conventional version of that is a hand-written
colouring plus a hand-written checker, where nobody checks the checker.

## The seams, stated plainly

An integration claim with no recorded seams is not credible. These are the ones
measured today, not the ones we can imagine.

### S1 — The Lean boundary is NOT bridged. Measured, not suspected.

This is the biggest one, and it is the joint the field cares most about: SAT
search and formal proof are separate worlds, and bridging them has taken years
of bespoke effort per result (Keller's conjecture, the empty hexagon number).
axeyum has both sides in one repository, which is exactly why the seam is worth
measuring rather than asserting.

`lean proofs/shell_closed_form.lean` against the pinned Lean 4.30.0:
**22 errors, exit 1, 0.175 s.** Three causes — recursor-based `def`s needing
`noncomputable`, `Eq.{u}` emitted inside `Eq`'s own constructor (19 of the 22
errors are that one cascade), and inductives declared with every argument as an
*index* while the emitted `Eq.rec` applications assume *parameters*. Our kernel
generates a recursor consistent with its own declaration form and accepts the
module; Lean generates a different one and does not.

Repairing all three still fails, because `lean file.lean` runs the
**elaborator**, not the kernel. The route is `lean4export` 3.1.0 — which
`axeyum-lean-import` already consumes fail-closed, making the round-trip a free
differential test. Until that writer exists, the two halves of the framework are
adjacent, not connected. Full detail: `FEEDBACK.md` F-C1, and
`docs/plan/lean-export-external-validation-2026-08-13.md` at commit `febbcc991`.

Related: `#print axioms shell_closed_form` — the line that would establish the
`0 axiom` property mechanically — **has never executed**.

### S2 — Ownership is not isolation

Three agents with disjoint file ownership still could not build independently,
because a shared checkout has one shared compile state. agent-c owns no shared
source file and was still blocked by agent-b's mid-edit. Snapshot-per-agent
(`git archive HEAD`) is now campaign rule 7. Also learned the hard way:
`rsync -a` of a live `.git` while another agent writes it yields
`fatal: bad object HEAD`.

### S3 — Route A does not cover the tree case

`compose_cover_proof`, which collapses a cover into a single DRAT proof of the
original formula and discharges the meta-argument entirely, is not generalized
to adaptive trees. Tree covers therefore rest on four checked obligations plus
a meta-argument rather than on one composed proof. Recorded by agent-b as a gap
rather than papered over.

### S4 — Work still happens outside the framework, some of it correctly

agent-a prototyped the subsumption reduction in a throwaway enumerator.
agent-c wrote the equation-renaming verifier in Python — deliberately, for
independence, which is the right call and should be labelled as such rather
than counted as a gap. The coordinator's feasibility table was a standalone
Python script, and it was **wrong**: it counted all solution multisets when the
encoder needs only the subset-minimal antichain, overstating one cell by 33x
and thereby deciding which cells an agent was allowed to attempt. Analysis done
outside the framework does not inherit the framework's checking.
