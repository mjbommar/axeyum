# One stack, eight stages — agent-b, `R_4(5(x-y)=4z)` at `n = 741`

A record of which axeyum component did each stage of this attack, and what a
conventional pipeline uses instead. Written from what actually ran today
(2026-08-13). The cover closed: `R_4(5(x-y)=4z) = 741`, both sides
machine-checked. See RESULT.md for the census and for the caveats.

## The stages

| # | stage | axeyum component | conventionally |
|---|---|---|---|
| 1 | model the problem | `axeyum_search::family::Rado` behind the `ColouringFamily` trait: the parameterised constraint enumeration **and** a brute-force enumerator written from `a(x-y)=bz` itself, deliberately sharing no code | a per-problem Python script |
| 2 | encode to CNF | `ColouringProblem::encode` -> `axeyum_cnf::CnfFormula` | a hand-rolled DIMACS emitter |
| 3 | split into cubes | `cover::colour_branch_plan` + `harness::run_adaptive_cover` (budget-driven adaptive trie) | `march_cu`, or a shell loop over a fixed product |
| 4 | search | `axeyum_cnf::solve_with_drat_proof_with_limits`, the in-tree CDCL core (ADR-0012) | kissat / CaDiCaL |
| 5 | produce proofs | the same call — the core emits DRAT as it learns; `TextProofSink` streams it for the monolithic route (ADR-0381) | the SAT solver's `--proof` flag, a separate file per cube |
| 6 | check proofs | `check_drat_backward` (ADR-0382), run inline in the worker that produced the proof | `drat-trim`, run later, out of process |
| 7 | compose the cover | `cover::verify_cube_cover` + `cover::certify_tree_cover` — four obligations, all checked | **usually nothing**: an assumption in the driver script |
| 8 | record the claim | `artifacts/claims/rado/...` + `scripts/check-claim-certificates.py`, kind `cube-tree-cover` | a README, or a table in a paper |

Two supporting stages that are usually improvised entirely:

| | stage | axeyum component | conventionally |
|---|---|---|---|
| a | satisfiable side | `search::min_conflicts`, then replay through `ColouringFamily::first_violation` before the witness is allowed to be called one | a local-search binary plus a hand-written checker |
| b | resume / partition | `rado_cover_gaps` reconstructs the maximal uncovered cubes from the ledger; `under=` filters them into a disjoint host partition | shell bookkeeping, or restarting |

## 1. The cover obligation moved with the search strategy

The flat cover could not finish `F_741`. So splitting changed: a cube that
exhausts its conflict budget is now split on the next branch point and its
children queued (`run_adaptive_cover`). The cover stopped being the cartesian
product and became a tree.

**Obligation 3 changed in the same commit.** It was
`verify_cell_set`: *the recorded cells are exactly the product `[1..k]^d`, each
once*. It is now `verify_cube_cover`: *the recorded cubes are exactly the leaf
set of a complete branch trie* — walking from the root, every node is either a
recorded cube or has all `k` children present, recursively. Failure modes are
named and distinguished: a hole reports the **largest** uncovered node
(`MissingCell`), a cube strictly inside another reports the buried one
(`DuplicateCell`). Both have negative controls that must fail closed, in
`cover.rs` and again as committed claim-ledger fixtures.

Had these been separate programs, the change would have been: edit the cubing
tool, and leave the question "is this set of cubes still a cover?" where it
usually sits — as an assumption in the driver script, since the cube file and
the refutations are produced by different programs by different authors and
nothing in between re-reads both. The mixed-depth cube list would have looked
exactly like the flat one to every downstream stage. The specific thing that
integration bought here is that *changing the search strategy could not
outrun the completeness check*, because they are one commit and one test suite.

### What the missing artifact turns into downstream

The sharper version of this, from the campaign's source audit of the one other
active group in this family (A. C. Li, SSRN 6814341, artifacts at
`crabsatellite/rado-numbers-sat`, CaDiCaL 1.5.3 through PySAT): their Lean
development takes the solver results in as an **axiom** —

```lean
axiom lem_keypair_sat (b k : ℕ) ...
```

— justified by a doc comment recording that the runs were "all UNSAT under
CaDiCaL 1.5.3". They are open about it; there is an `AxiomAudit.lean`. But
every downstream theorem is then conditional on an uncertified solver run.

That is the honest end state of a pipeline in which no artifact corresponds to
the claim. For a cube cover the missing artifact is specifically *"these cubes
are exactly a cover"*: there is no file, no checker, and no failure mode for
it, so it survives as an assumption in a shell script and arrives in the proof
assistant as an axiom. `verify_cube_cover` plus `certify_tree_cover`, the
shape-independent cube codes that make a resumed run one cover rather than two,
and the negative controls that fire on an incomplete or overlapping one **are**
that artifact. They are the part of this result that does not otherwise exist.

The honest caveat belongs in the same breath: see the route-A seam below. This
cover's final step is discharged by four checked obligations, not by a checker
accepting one composed DRAT proof, so it is a *checked* meta-argument rather
than no meta-argument at all.

## 2. Resumability turned out to be a soundness property

To use two hosts on one tree, a run has to stop, be partitioned, and resume.
Two decisions made that safe, and both only make sense when the harness, the
ledger format and the checker are one system:

* **Cube codes do not depend on the tree's shape.** `BranchPlan::prefix_code`
  lays levels out consecutively and reads each tuple mixed-radix, so a cube's
  identity is a function of the plan and the path alone. Two runs that split
  the same subtree differently still agree on the identity of every cube they
  share, and their ledgers concatenate. Had codes been positions in a walk of
  the cover, a resumed run would have renumbered everything and the union would
  have been meaningless.
* **Ledger rows are written only for refuted cubes** (plus a satisfiable one,
  which ends the question). A cube that is split or stuck goes to the pending
  file instead.

The second is the interesting one. Finding B2 of the previous session was a
restarted run appending to a live ledger — 1093 rows over a 1024-cell product,
69 duplicates — and the detector installed against it rejects a repeated cell
index *whatever run ids the rows carry*. If a resumed run recorded its
`resource-out` cubes, and a later run refuted one of them, the union would
carry two rows for one cube and that detector would fire **on a correct
cover**. The predictable next step is that someone relaxes the detector, and
then it no longer catches the thing it exists for. Avoiding the false positive
was a deliberate design choice, not a convenience.

The complement is measured, not assumed: the partition was checked by an
independently written Python trie walk before either host was launched — 829
refuted cubes plus 96 gaps, zero overlaps, zero holes, every leaf reached,
**total measure exactly 1**.

## 3. Where the integration did NOT help — the seams

* **Route A does not survive an adaptive cover — the one seam that matters.**
  `compose::compose_cover_proof` turns a flat cover into a single DRAT proof of
  the original formula, whose acceptance discharges the whole result with no
  meta-argument at all. Its collapse loop walks `prefix_count(level)` for every
  level, so it assumes every leaf sits at full depth; a tree cover has leaves at
  mixed depths and it does not handle them. Consequence, stated plainly:
  **this result is route B.**

  The generalization is specified in FEEDBACK.md item 1: the per-cube lift is
  unchanged, and the collapse becomes a bottom-up walk of the *actual* trie's
  internal nodes (children strictly before parents), emitting `R(p)` for each.
  The RUP argument survives because completeness of the trie is exactly what
  guarantees each child's clause is already in the database. The transform is
  small; what is *not* small is that at this instance's scale the composed
  proof is ~58 GB, so route A here also needs streaming composition and a
  checker that can verify a proof larger than memory. Until that exists, large
  covers stay route B and should say so. The final step — *checked refutations of every cube of an exhaustive
  cover imply the formula is unsatisfiable* — is discharged by four checked
  obligations, not by a checker accepting one proof. (FEEDBACK.md item 1.)
* **The claim ledger's vocabulary lagged the harness.** `check_cube_cover`
  requires `k**d` cells each fixing every branch integer, so a finished
  adaptive cover could not have been recorded at all. The capability and the
  evidence vocabulary had drifted apart silently, and nothing failed until
  someone tried to record one. Fixed additively today (`cube-tree-cover` plus
  two negative fixtures), but the drift is the point. (FEEDBACK.md item 10.)
* **One encoder had no gate, and its doc comment said it did.**
  `axeyum-search/src/colouring.rs:10` cites `tests/encoding_parity.rs`, which
  does not exist in that crate; the real gate covers a different encoder in
  `axeyum-cnf`. Three encoders agree byte for byte on `F_741` — that was
  measured today — but the citation was wrong for however long it stood.
  (FEEDBACK.md item 8.)
* **The backward checker has a ~0.59 s fixed cost per call** on this formula,
  independent of proof length, because it re-prepares the clause database each
  time. At tree-cover scale that is a major cost centre for proofs that are a
  single propagation conflict. Integration made it *visible*; it has not yet
  made it cheap. (FEEDBACK.md item 2.)

## 4. The OOM that did not happen

`F_313` was refuted monolithically at 60,543,837 steps and 5.0 GB of text
DRAT, and needed ~28 GiB — it was OOM-killed at exit 137 on 26-27 GiB hosts,
which reads exactly like a refuted claim and is not one. `F_741` is much
larger.

What kept this run away from that edge was measurement inside the framework
rather than a rule of thumb:

* text DRAT here costs about **83 bytes per step** (confirmed against the 313
  figures and today's own step counts);
* the s4 run passed **40.8M steps in its first 11 minutes**, so dumping every
  cube's proof would have written ~3 GB per 11 minutes per host, on a 384 GiB
  disk, while two hosts ran for hours;
* backward checking costs about as much as solving (0.95 ratio, measured:
  1012.3 s solve against 957.8 s check over 362 cubes).

So the runs check each proof **inline, in the worker that produced it, and
keep no proof bytes at all**. Nothing accumulates in memory or on disk; the
artifact is the cube list, and `rado_replay_tree_cover` regenerates every proof
from it — validated on the `F_103` cover, where a replay on a different worker
count reproduced **1,137,228 proof steps, identical to the digit**.

That option exists because two framework-level fixes came out of the previous
session's own bottleneck: the streaming DRAT sink (ADR-0381), so proof
production is not bounded by memory, and the backward checker (ADR-0382), so
checking a cube costs seconds rather than minutes. agent-c hit the same wall
from the other side today and killed a monolithic run at 2.6 GB of DRAT with
RSS tracking it, rather than let it OOM at hour three and look like a result.

## 5. The integration check that caught a mistake of mine

Re-partitioning the tree across hosts leaves an obvious way to corrupt the
result: a run that is stopped and restarted from a *wider* starting point
refutes cubes that the restarted run will refute again, and the union then
covers part of the space twice. That happened here — a run named `c4` refuted
111 cubes before being replaced by one starting from the whole quarter.

The union is checked for exactly this: `rado_cover_gaps` over every ledger
reports an overlap and refuses, rather than pruning it. Over the seven ledgers
that make up the finished cover it reports no overlap and
`covered 4294967296/4294967296` — an exact ratio of integers, not a rounded
percentage. The offending ledger is quarantined, not deleted.

The reusable part: because the ledger format, the gap reconstruction and the
completeness obligation are one system, "did I just contaminate the union?" is
a command that takes a second, and it is the same code path that will issue the
final certificate. In a fragmented pipeline that question is answered by
remembering.

## Status

**The cover closed.** 6241 cubes, covered measure exactly
`4294967296/4294967296`, 699,572,027 proof steps, every one checked by
`check_drat_backward` in the worker that produced it, zero deferred, zero
failures. With the banked witness at 740, `R_4(5(x-y)=4z) = 741`. See
RESULT.md for the full census and for what is *not* claimed — in particular
that this is route B, so the last step is four checked obligations rather than
a checker accepting one composed proof.

Every stage in the table above ran inside axeyum. The stage that has no
conventional counterpart at all — row 7, "is this set of cubes actually a
cover?" — is the one that had to change when the search strategy changed, and
it is the one that would have become an axiom downstream.

Independent re-derivation, since an integration claim should be measurable:
`rado_replay_tree_cover` rebuilt every one of the 6241 refutations from the
ledger alone on two hosts, two worker counts and **two rustc versions**
(1.99.0-nightly and 1.93.1 stable), and both produced 699,572,027 proof steps
identical to the digit. That is one command against one artifact, and it is the
same code path that issued the certificate.
