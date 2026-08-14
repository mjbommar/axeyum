# Coordinator diary — frontier campaign, 2026-08-13

## 15:xx — Setup

Read the Rado session diary, the findings register, the claim ledger (38 claims,
2 open frontier records), both sibling repos, and `axeyum-search`. Searched for
live open problems that fit the machinery. Wrote the top-10 for the user.

The filter that decided the list: **the lower bound must already be free or a
published theorem, so the only missing artifact is one certified refutation.**
That is exactly the shape `axeyum-search` discharges.

Fleet probe:

| host | cores | RAM total / avail | load |
|---|---:|---|---|
| s0 (server0, local) | 24 | 123 / 73 GiB | 8.9 |
| s1 | 4 | 61 / 50 GiB | 0.0 |
| s4 | 16 | 123 / 121 GiB | 0.0 |
| s5 | 16 | 27 / 26 GiB | 0.1 |
| s6 | 16 | 26 / 25 GiB | 0.0 |
| s7 | 16 | 26 / 19 GiB | 0.1 |

`/nas3/data` (nfs4, 16 TB free) and `/nas4/data` (25 TB free) are mounted on
every host. Campaign workspace at `/nas3/data/axeyum/frontier-2026-08-13`.

Note for the record: the previous session measured `recertify_rado` needing
~28 GiB and being OOM-killed at exit 137 on 26-27 GiB boxes. s5, s6 and s7 all
have ~26 GiB. **Any monolithic recertification must run on s4 or s0**, and exit
137 on the small boxes must not be read as a refuted claim.

## Batch 1 — three agents

- **agent-a — off-diagonal Schur.** `S(3;s,t,u) = stu-tu-u-1` (Ahmed-Schaal
  Conjecture 2, open since 2015, live in arXiv 2604.11030 of April 2026).
  Lower bound is Ahmed-Schaal Thm 2.11, so each open cell needs one refutation.
  Ten open cells under 50M clauses; smallest is `S(3;4,4,8) = 87?` at 2.6M.
  Needs a per-colour extension of `ColouringFamily`, which is today the only
  code change on the critical path.
- **agent-b — `R_4(5(x-y)=4z) = 741`.** The repository's own open frontier
  claim. Depth-6 probe left 746/4096 refuted, 1132 resource-out, 2210
  unstarted; the recorded diagnosis is adaptive deeper splitting.
- **agent-c — `R_k(a(x-y)=bz) = a^k` for `gcd(a,b)=1, a >= b+2`.** The k-
  generalization of a Chang-De Loera-Wesley theorem proved for k=3 only.
  Confirmed at k=4 twice by our own ledger. `R_5(3(x-y)=z) = 243?` would be the
  family's first exact five-colour value.

Clause counts for agent-a's table were computed here, not guessed:
`scratchpad/sizes.py`, exact partition DP.

## 16:xx — The Lean item, taken by the coordinator because nobody owns it

Item 5 of the top-10 was "one command converts *we emitted a Lean module* into
*an independent kernel accepted it*". I ran the command. It does not.

Order of discovery, which is the useful part:

1. Checked for a toolchain expecting to install one. **It was already there** --
   `~/.elan/toolchains/leanprover--lean4---v4.30.0`, matching the repo's own
   `lean-toolchain` pin. `elan` is absent and `lean` is not on `PATH`, so
   `which lean` fails, and that negative probe is what the earlier audit
   recorded as "the toolchain is absent (verified)". A negative probe read as a
   fact about the machine. Straight onto the CLAUDE.md tools-lie list.
2. Ran `lean proofs/shell_closed_form.lean`: **22 errors, exit 1, 0.175 s.**
3. Peeled it: codegen (`noncomputable`), then a self-reference emitting
   `Eq.{u}` inside `Eq`'s own constructor (19 of the 22 errors are this one
   defect cascading), then the real one -- the emitter declares `Eq` with `alpha`
   and `a` as **indices** while every `Eq.rec` application in the module assumes
   **parameters**. Our kernel generates a recursor matching its own declaration
   form and accepts it; Lean generates a different one and does not.
4. Even with both fixed, elaboration fails reaching for `CoeFun`. That is the
   finding: **`lean file.lean` is elaboration, not a kernel check.** Surface
   syntax makes the artifact hostage to implicit inference, universe
   unification, coercions and codegen -- none of which bear on whether the
   proof term is well-typed.

The fix is symmetric with something we already do right: `axeyum-lean-import`
consumes official `lean4export` NDJSON 3.1.0 fail-closed. The export side should
emit that same format and be validated by `leanchecker` (which ships in the
pinned toolchain) -- then the round-trip through our own importer is a free
differential test.

Also noted: `#print axioms shell_closed_form`, the line that would establish the
`0 axiom` property mechanically, **has never executed** -- the cascade prevents
the theorem from being declared at all. The property is real but it was
established by reading the text.

Wrote `coordinator/FEEDBACK.md` (F-C1, five actionable items L1-L5) and
`coordinator/logs/lean-export-check-2026-08-13.md` (full reproduction).

I did not modify `proofs/shell_closed_form.lean`. All experiments were on copies
in the scratchpad; the paper's artifact is untouched.

## 19:50 — process finding from agent-c, worth more than it looks

agent-c owns no shared source file, by design. It still could not build
`axeyum-search`, because agent-b is mid-edit in `cover.rs` and the shared
worktree does not compile. It worked around this with a `git archive HEAD`
snapshot in its own scratchpad.

The file-ownership map prevents agents from *clobbering* each other. It does
nothing about the fact that a shared checkout has a single, shared compile
state. **Ownership is not isolation.** For batch 2 the instruction should be:
build from your own `git archive HEAD` snapshot by default, and only touch the
live worktree when committing.

The memory note says no side branches or worktrees, so snapshot-per-agent is
the right shape here rather than `git worktree`.

Also from agent-c, and it is the most valuable thing anyone has produced so far:
A. C. Li (SSRN 6814341, 2026) reportedly claims `R_5(3) > 296` for `x+by=bz`,
which is the same family under renaming and therefore says
`R_5(3(x-y)=z) > 296 > 243` -- i.e. it would REFUTE the `a^k` prediction at
k=5. Not peer reviewed, full text unread. agent-c is testing both sides rather
than assuming, which is exactly right.

## 19:57 — a soundness trap in agent-a's target, caught by reading a diff

Saw `scopes` / `symmetry_blocks` / `per_colour` appear in
`crates/axeyum-search/src/colouring.rs` and checked what they were for before
assuming. (I had first attributed the edit to agent-c from the diagnostics
alone and was wrong -- read the diff, then corrected the message I had already
sent.)

The point matters: **colour-symmetry breaking is unsound for off-diagonal
instances.** In the diagonal families the k colours are interchangeable, so
"colour i first appears before colour i+1" is free. In `S(3;s,t,u)` with
s, t, u not all equal, each colour forbids a *different* equation, the colours
are not interchangeable, and the ordering constraint can cut away real
solutions -- turning a satisfiable instance into a spurious UNSAT. That is a
wrong-unsat, the exact failure class this project exists to prevent.

agent-a's `symmetry_blocks` looks designed for this (permute only within blocks
of equal `k_i`), so the design is right. I asked for two things that turn it
from designed-right into shown-right:

1. make sure `(4,5,6)=83` and `(4,5,7)=97` are in the regression set actually
   run -- three distinct equations, therefore **no** colour symmetry at all, so
   an over-strong break shows up there first;
2. a negative control that deliberately applies the unblocked ordering
   constraint to a known instance and confirms it produces a **wrong** verdict.
   A symmetry break that cannot be shown to break something when misapplied has
   not been tested.

This is the generalisation cost nobody budgets for: the encoder's symmetry
breaking was correct for every family the trait could previously express, and
becomes incorrect the moment the trait can express a second kind of family.

## 20:11 — check-in. Two findings, one of them the headline.

### agent-c: the `a^k` law is REFUTED at k = 5

`R_5(3(x-y) = z) > 243 = 3^5`. Cell 137 of a depth-6 cover, cube [1,1,2,1,3,3],
came back **satisfiable in 35.8 s**. So the natural generalisation of CDLW's
`R_3 = a^3` -- the target I sent agent-c to confirm -- is false.

Checked four ways, none of them the searcher: the harness's own
`ModelDoesNotSatisfy` guard; a Python decoder + O(n^2) enumerator written from
`3(x-y)=z` with no axeyum code (16,362 triples, 0 monochromatic); the crate's
independent `first_violation`; and a *second searcher* (the batsat adapter)
which found a **different** satisfying assignment at 457.8 s. Two searchers,
one verdict.

This is the pattern the project prizes: a prediction, made precise enough to
fail, refuted by the same machinery that produced it -- inside 90 minutes.

agent-c's novelty handling is exactly right and I want it recorded: it does
**not** claim the bound as new, because an unread June 2026 SSRN preprint
appears to report `R_5(3) > 296`, and it verified the equation renaming
mechanically (49/49 hypergraph identity checks) rather than trusting its own
algebra. What is ours is that the verdict is certified end to end inside
axeyum with no external solver. That is the honest claim and it is still worth
having.

Two by-products worth as much as the result:

- **The Table 10 census is now exact**: 20 cells, 13 populated, but only **12
  exact** -- `(2,3)` was the bare `> 225` we closed last session. Blank:
  (5,2), (4,3), (5,3), (2,4), (3,4), (4,4), (5,4). So `R_4(5,1)=625` is
  *published* (replication), while **`R_4(5,2)` and `R_4(5,3)` are blank** and
  would be genuinely new four-colour values. agent-c has redirected there.
- **A warm start is a bias.** min-conflicts from the valuation colouring failed
  three times at n=243; the harness, which starts from no construction, found
  the witness in 36 s. The valuation colouring provably cannot extend to 243
  (whichever class 243 joins produces a monochromatic solution -- e.g.
  `{82,1,243}`), so the warm start was a bias *toward failure*. Cheap check
  first: can the construction be extended at all?

### agent-a: the clause counts I gave it were wrong by up to 33x

Subsumption. A solution multiset's clause is `not-all-same-colour` over its
distinct members; if `S` is a subset of `S'` then `clause(S)` subsumes
`clause(S')`, so only the subset-minimal antichain is needed. Measured:

| k | n | all multisets | minimal antichain | ratio |
|---|---:|---:|---:|---:|
| 4 | 43 | 2,282 | 1,870 | 0.82 |
| 8 | 87 | 2,576,807 | **77,314** | **0.030** |
| 6 | 160 | 7,976,497 | 2,838,602 | 0.36 |

`S(3;4,4,8)` is ~111k clauses, not the 2.6M I computed. The reduction is
strong exactly when `n/(k-1)` is small. My feasibility table (`sizes.py`)
counted *all* solution multisets and is superseded -- and it was the thing
that decided which cells agent-a was allowed to attempt. Every "TOO BIG" row
with a large `u` needs recomputing; the whole `S(3;4,4,u)` row plausibly opens
up. Telling agent-a now.

Lesson for me: I sized the work with an exact computation and still got it
wrong, because I computed the right quantity for the wrong encoding. An exact
number is not the same as the relevant number.

## 20:38 — check-in. agent-a has eleven new values; the conjecture survives.

**Ahmed-Schaal Conjecture 2 survives 22 for 22.** Eleven published values
reproduced (the regression gate, 119 s of wall clock on one 16-core host) and
**eleven values nobody had computed**, every one agreeing with
`s*t*u - t*u - u - 1` exactly. No mismatch.

```
S(3;4,4,8)  = 87     S(3;4,5,8)  = 111    S(3;5,6,6)  = 137
S(3;4,4,9)  = 98     S(3;4,6,7)  = 118    S(3;4,7,7)  = 139
S(3;4,4,10) = 109    S(3;5,5,7)  = 132    S(3;5,5,8)  = 151
S(3;4,4,11) = 120    S(3;4,5,9)  = 125
```

Both sides discharged on every row: `n = N-1` sat with the model replayed by an
independent reachability search AND re-checked against the **full unreduced**
solution list, `n = N` unsat with a DRAT proof re-derived by our own backward
checker. No kissat, no drat-trim, nowhere.

### The negative control is the best single artifact of the campaign

agent-a's committed control
`whole_palette_symmetry_breaking_produces_a_wrong_unsat` shows the unblocked
symmetry breaking turning a **satisfiable** `S(3;3,4,5)` at `n = 41` into
`unsat`. And the sentence that matters: *four other instances it tried did not
flip*, so a control built on any of those would have passed while testing
nothing. That is the difference between having a negative control and having a
negative control that works -- and it is exactly the failure mode this
repository keeps rediscovering (a gate that runs zero tests and exits 0).

### My feasibility table was wrong in the most consequential direction

The cells I excluded turn out to be **the cheapest direction in the table**.
`S(3;4,4,10)` reduces 46,281,800 multisets to 239,130 clauses -- ratio 0.005 --
because the only two-element solution sets of `L(k)` are `{a,(k-1)a}`, there are
`floor(n/(k-1))` of them, and every solution set containing such a pair dies to
one. Large `u` with moderate `n` is the cheapest infinite direction; the
multiset count says the opposite. Had agent-a obeyed my table it would have
stopped at ten cells; it opened an extended lane and has produced three more
values from it so far, with thirteen queued.

**The wall has moved.** Every instance above is decided by the CDCL core in
under 2 seconds; *building the constraint list* takes 40-160 s. `S(3;4,4,10)`
spends 110 s enumerating to keep 239,130 clauses that are then refuted in
0.03 s. The bottleneck of this problem class is now enumeration, not search --
which is a statement about the framework's shape, not about the mathematics.

### agent-b: `F_741` past half

53.92% of the assignment space refuted with checked proofs, 2033 cubes, across
three ledgers whose **union** is replayed as one cover (`rado_replay_tree_cover`),
with negative controls for both failure modes: the same file twice gives
`duplicate-rows rows=800 distinct=400`, one half alone gives
`cover is missing cell 846`. Shared tree compiles again now that agent-a's
`colouring.rs` landed: 65 tests pass, clippy clean.

### agent-c: a measurement that explains the whole memory story

**6.6x blow-up from text-DRAT bytes to resident memory during checking** --
1,873,245,421 bytes of proof, 12.3 GiB resident. agent-c's own earlier estimate
was 1.5x; the measurement is four times worse. This is *after* ADR-0381 made the
producer streaming, so it is the checker's retention, not the emitter's. It is
the precise reason a 26 GiB host cannot certify what a 61 GiB host can, and it
retires guesswork about the OOM class with a number.

Also recorded: `top` confirmed 100% CPU, worth stating because a constant RSS
and a silent log look exactly like a stall.

### Process note from agent-a, learned the same way we learned it before

It had to kill a running s5 lane to deploy a faster binary, and moved the old
log aside as `extended-s5-abandoned-old-binary.out` rather than let the new run
append. Two runs interleaved in one log is how a ledger ends up with 1093 rows
over a 1024-cell product.

## 21:xx — Literature and source audit. I should have done this first.

Prompted to contextualise the results against the literature and other source
code before believing our own novelty claims. Two hours of compute would have
been spent differently if I had done this at hour zero. Findings, in the order
they mattered.

### 1. Song-Mao has a Table 3 that neither I nor agent-a had seen

I had read arXiv:2604.11030's abstract and its **Table 2** (the eleven
Ahmed-Schaal values) and built agent-a's brief on that. Extracting the **full
text** turned up a **Section 5, "Computer-assisted exact values on finite
ranges", with Table 3** -- their own new exhaustive search, published April
2026:

```
S(3;3,3,8..15)  = 59, 68, 77, 86, 94, 104, 113, 122
S(3;3,4,8..12)  = 67, 78, 86, 98, 106
S(3;3,5,8..10)  = 91, 103, 115
S(3;4,4,8) = 87,  S(3;4,4,9) = 98,  S(3;4,4,10) = 109
S(3;4,5,8) = 111
S(3;4,6,7) = 118
```

**Five of agent-a's eleven "new" values are in that list** -- (4,4,8), (4,4,9),
(4,4,10), (4,5,8), (4,6,7) -- and **every one matches ours exactly**.

Six survive as genuinely new: (5,5,7)=132, (5,6,6)=137, (4,7,7)=139,
(4,4,11)=120, (4,5,9)=125, (5,5,8)=151.

This is the Znam-1966 trap of the last session, and it was one web fetch away
the whole time. It also **improves** the result: the regression gate is now
**16 published values reproduced with zero mismatches**, five of them against
an independent April 2026 computation by a different group on a conventional
SAT pipeline. That is external cross-validation of our encoder on exactly the
cells where a wrong-UNSAT would be invisible.

Their Section 5 describes their encoding (`v_{i,c}`, exactly-one-colour,
clauses forbidding monochromatic `L(r)`) with **no subsumption reduction**,
which is plausibly why their frontier stops at (4,4,10) and ours is past
(4,4,11). If so, agent-a's 0.005-ratio reduction is a citable methodological
result rather than an internal optimisation.

Also picked up: their **Theorem 6**, `S(3;s,t,u) <= R_3(s,t,u) - 1`, by a clean
difference-colouring argument, and **Corollary 8**, an asymptotic bound for
large u. Neither threatens our values. Checked and dismissed as irrelevant:
arXiv:2608.08789 (9 Aug 2026), "Restricted generalized Schur numbers" -- a
different object `S_r(k;l)`, 2-colour closed form, no `S(3;s,t,u)` table.

### 2. `gh` found Li's artifacts, which SSRN would not give us

agent-c's caution flag rested on search-engine summaries because SSRN 403s
every fetch. The paper's **public repository does not**:
`crabsatellite/rado-numbers-sat`, MIT, Zenodo DOI 10.5281/zenodo.18957993,
citing `li2026rado` / SSRN 6814341.

It ships `data/results/R5_witness_243.json` -- an explicit witness at n=243.
So **agent-c's refutation is confirmed as a reproduction**, exactly as agent-c
assumed without being able to read the source. Their README is careful: "the
exact value is not claimed."

`main_results.json` (2026-03-10, CaDiCaL 1.5.3 via PySAT, i7-12700K/64GB):

- refined conjecture `R_k(x+by=bz) = b^k` **iff** `k <= 2(b-1)`;
- upper-bound status in their words: "k=1 trivial, k=2 Landman-Robertson 2014,
  k=3-4 Key Lemma + SAT, **k>=5 OPEN**";
- **b=6: R null, "n=1295 SAT confirmed, n=1296 UNSAT needs cluster"**;
- b=7: "too large for desktop".

Two of agent-c's targets are therefore open **by the authors' own admission**,
and one of them is blocked on precisely the resource we have. Reprioritised
agent-c onto `R_4(6(x-y)=z) = 1296` and `R_5(4(x-y)=z) = 1024`. Our `(5,2)` and
`(5,3)` are untouched by Li -- their family maps onto our `b=1` column only.

### 3. The most important finding of the audit: their Lean bridge is an axiom

`lean4/RadoNumbers/SAT.lean` contains

```lean
axiom lem_keypair_sat (b k : ℕ) (hbk : ...) ...
```

with a doc comment reading *"Justification: SAT verification (Li 2026 ...).
Separate SAT check for each color, all UNSAT under CaDiCaL 1.5.3"* and a status
line `gapOpen Cat 2 SAT-verified`. Their `AxiomAudit.lean` reports it honestly.

So the state of the art for this exact problem is: **the SAT result enters Lean
as an assertion, and every downstream theorem is conditional on it.** They are
transparent about it, which is to their credit -- and it is exactly the seam
axeyum exists to close.

That gives us a precise, defensible position instead of a vague one:

| | SAT side | bridge to a proof assistant |
|---|---|---|
| Li 2026 | CaDiCaL, no certificate mentioned | `axiom`, audited and labelled `gapOpen` |
| axeyum today | own CDCL, DRAT, own backward checker, replayed | **broken in the export direction** (seam S1) |

Neither project has closed the loop. Ours is certificate-backed where theirs is
an axiom; theirs reaches Lean where ours does not. **Closing S1 is what makes
the difference real rather than rhetorical**, and it moves batch 2's Lean agent
from "nice to have" to the campaign's highest-value remaining item.

Sobering, and worth writing down: the "SAT + Lean + claim ledger" architecture
we thought was distinctive is also what a solo preprint author built this
March. The architecture is not the moat. The checked certificate is.

### 4. Repos worth knowing

- `laminazaman/RadoNumbers` -- Ahmed-Zaman-Bright's AutoCase symbolic analyser
  (their SC^2 2025 paper's artifact).
- `crabsatellite/rado-numbers-sat` -- Li, above.
- `jontitan1/schur-numbers-sat-solving` (2026-08-01) -- not yet examined.

### 5. Negative literature results, recorded so nobody redoes them

- **`R_4(5(x-y)=4z) = 741` and `R_4(6(x-y)=5z) = 1501`: no prior art found.**
  Direct searches return only unrelated Rado families (Malo's SDSU thesis on
  four-colour `x1+x2+c=x3`, Myers's Rutgers thesis, the two-colour
  `a(x+y)=bz` literature). CDLW Table 10 leaves `(5,4)` blank, and Li's family
  covers only our `b=1` column. agent-b's target is open and uncontested.
- `jontitan1/schur-numbers-sat-solving` (2026-08-01) is **not** a conflict with
  agent-a: it is weakly-palindromic monochromatic Schur triples and modular
  MSTs (Millsaps College, testing a Fredrickson-Sweet 2000 conjecture at
  N <= 160, five colours). Different object.
- arXiv:2608.08789 (9 Aug 2026) "Restricted generalized Schur numbers" is a
  different object `S_r(k;l)` with a 2-colour closed form; no `S(3;s,t,u)`
  values.

### 6. What I would do differently

The audit cost about twenty minutes and it moved two of three agents' target
lists. I ran it after seven hours of compute because I had read abstracts and
believed them. The specific failure: I read arXiv:2604.11030's **abstract and
Table 2** and built a brief on it, when the paper's own **Section 5 and Table 3**
were in the same PDF I had already downloaded to disk. I extracted the text for
Table 2 and stopped reading at the point my question was answered.

Standing rule for the rest of this campaign, and it belongs in the roadmap:
**before any run that will produce a novelty claim, extract the full text of
the closest paper -- not the abstract, not the first table that answers the
question -- and search GitHub for its artifact repository.** SSRN 403s; the
Zenodo/GitHub artifacts do not.

## 21:xx — Correction: I overstated the Lean seam, and the defect is smaller than I said

Challenged on why we need to export to Lean at all when we have our own
Lean-compatible kernel. The challenge was right and my S1 write-up was wrong in
one important respect. Checked rather than argued:

**The internal path exists and is closed.** `axeyum-solver` depends on
`axeyum-lean-kernel` (optional, enabled by the `full` feature), and the
`reconstruct/` module family builds kernel terms that the kernel type-checks --
`reconstruct/resolution.rs:288` describes producing "a term of type `False`
that the trusted `axeyum_lean_kernel::Kernel` type-checks", and there are
in-tree `Kernel::new()` + `add_declaration` call sites across
`reconstruct/bitblast.rs`, `reconstruct/arithmetic.rs`, `word_reconstruct.rs`,
`regex_reconstruct.rs`, `int_reconstruct/counterexample_cover.rs`.

So there is no "export to our own kernel" problem: the proof term is *born*
inside the kernel and checked there. My line in FRAGMENTATION.md that "the two
halves of the framework are adjacent, not connected" is **wrong** and needs
correcting; it is true only of the outward direction.

**And the defect is a printer bug, not a kernel divergence.** I chased the
params-vs-indices mismatch to ground:

- `Kernel::add_inductive` and `add_mutual_inductive` take **`num_params:
  usize`** as an explicit argument (`inductive.rs:239-283`).
- `axeyum-lean-import` reads `numParams` straight from the lean4export wire
  format and passes it through, and even validates that mutual families agree
  on it (`lib.rs:855,896-899,917-923`).
- `lean_pp.rs` references `num_params` **zero times** (measured, not assumed).

`InductiveFamilySpec` does not carry `num_params` because it is a *group*-level
property -- which is correct, and matches Lean's own requirement that mutual
families share it. The kernel therefore holds `Eq` with its true parameter
count; the **printer** flattens the telescope and emits everything after the
colon, so Lean reads the declaration as zero-parameter, generates a different
recursor, and rejects the `Eq.rec` applications.

This is much better news than F-C1 implied. The fix for the readable projection
is "make `lean_pp` carry `num_params`", not "reconcile two kernels". I have no
evidence of a semantic divergence between our kernel and Lean's, and I should
not have written anything that reads as if I did.

**What the export is still for, and it is not checking.** Our kernel checking a
term our own reconstruction produced is circular from a referee's point of
view -- the same objection ADR-0002 answers for solvers by keeping z3 as a
differential oracle, and the same reason the slow forward DRAT checker is
retained beside the fast backward one. Independence is the product, not
capability. Note the import direction already supplies differential evidence in
one direction: our kernel admits Lean's own mathematics from official v4.30
exports. Untested is the reverse.

Revised item sizes: **L3 (printer carries `num_params`) is small and now
well-diagnosed**; **L1 (emit lean4export) remains the real deliverable**, for
third-party checkability rather than for our own confidence.

## 21:xx — agent-d launched: the Lean bridge

Fourth agent, briefly over the 2-3 concurrency guidance, on explicit
instruction. Justified because it is a compile-and-typecheck task rather than
fleet compute -- assigned **s0**, shared with me, so no other agent's host is
poached.

Scope, in priority order:

- **L3** -- make `lean_pp` carry `num_params` so parameters print before the
  colon; stop emitting explicit universe args on an inductive's self-reference;
  mark recursor-based defs `noncomputable`. Success is `lean <file>` exiting 0
  and `#print axioms shell_closed_form` **running for the first time**, not a
  diff that looks right.
- **L1** -- emit official `lean4export` NDJSON 3.1.0, the mirror of
  `axeyum-lean-import`. Validated by round-trip through our own importer
  comparing ADR-0350 canonical identity manifests. The strongest test I could
  think of and asked for explicitly: take each **official v4.30 fixture**,
  import, re-emit, re-import, and require the identity manifests to match --
  import-export-import over *Lean's own* output, so the emitter is tested
  against artifacts we did not author. Byte-identity is not the invariant; the
  manifest is.
- **L1b** -- external acceptance: scope it and stop. `leanchecker` wants
  `.olean`s, Lean 4.30 has no export flag, `lean4export` is not installed.

Told it explicitly that if surface syntax turns out to be a dead end for the
general case, **saying so with evidence is a legitimate result** -- L3 buys a
human-inspectable artifact, not a trust route, and I do not want it ground into
the ground for a cosmetic win.

### Coordination with the other lane

`ListAgents` shows a peer interactive session `axeyum-e8`, active, 22 hours old
-- almost certainly the author of the uncommitted WIP in
`crates/axeyum-lean-kernel/{env,inductive,lib,quotient,string_prelude,tc,tests}.rs`
(the R1/R2 Lean requirements track). Messaged it directly: told it exactly what
I committed (`febbcc991`, two files, pathspec-verified), that agent-d is scoped
to `lean_pp.rs` plus new files only, that all its WIP files are off-limits, and
offered to hold agent-d entirely if it would rather have the crate to itself
while its work is in flight.

Also passed on the two findings that bear on its track: the toolchain was never
absent, and the export failure is in the printer rather than the kernel. If
R1/R2 has been reasoning about Lean compatibility on the assumption that
`lean_pp` output is externally checkable, that assumption is now measured false
and it should know before I do anything else in there.

Worth noting for the record: this is the first time in the campaign that
coordination has crossed *outside* my own agent set. The file-ownership map
only ever covered agents I launched; a 22-hour-old peer session editing the
same crate was invisible to it until I looked at `ListAgents`. Ownership maps
need to start from `git status`, not from the roster.

## 21:xx — Peer corrections. Three land, and one of mine was imprecise.

The peer session replied and it was worth every minute of the outreach.

**1. I named the wrong owner.** The kernel-crate WIP is a **third** session,
driven by the codex CLI (PID chain 3496769,
`--dangerously-bypass-approvals-and-sandbox`), which landed `f2ccc4322`
(ADR-0387) and `73bce3646` and is currently running
`cargo test -p axeyum-solver --features full`. The peer is review-only there.
So my ownership map was wrong in the specific way I had warned about an hour
earlier: I inferred an owner from a roster instead of from process state. I
have re-pointed agent-d's off-limits instruction at the codex session and told
it that owner is unreachable -- so it must simply not touch, not wait.

**2. My "22 errors" was imprecise, and the breakdown matters.** Measured split:
**15** universe-parameter errors, **5** codegen/`noncomputable`, **2** unknown
identifier/constant. The 5 codegen diagnostics are Lean trying to emit
*executable code* for recursor-based definitions; they say nothing about
whether the proof checks. Reporting them inside a single "22 errors" figure
overstates the failure. Propagated the corrected phrasing everywhere.

**3. Their root-cause split is better than mine, and my experiment corroborates
it.** Two defects in one declaration: (a) the flattened parameter telescope
(my `num_params` finding, confirmed) and (b) the explicit `.{u}` on the
self-reference inside `Eq`'s own constructor, which Lean rejects because the
inductive under elaboration is a local. With (b) present Lean never reaches
the recursor stage, so **one root cause, not fifteen**. My sequential patching
is independent evidence of the ordering: removing (b) exposed the recursor
mismatch, patching (a) too moved the failure again to `CoeFun`. (b) masks (a);
both real; neither alone sufficient.

**4. The gift: `Environment.replay`.** `lean4export`'s parser is a library and
its output can be replayed into the **real C++ Lean kernel** (see
`leanprover/comparator`). That is genuine third-party *kernel* acceptance, not
elaboration -- it converts L1b from "scope it and stop" into a real route.
Trap passed on verbatim: delete `Quot.mk`/`Quot.lift`/`Quot.ind` before replay
or the kernel errors on double-add.

**5. `AXEYUM_LEAN_BIN` confirmed.** Eight suites consult it and **skip**. Their
own R0.1 already requires that no Lean gate may pass by being inert -- that
requirement now has a live instance instead of a hypothetical one: the suites
have been skipping on a host where the toolchain works. Queued for agent-d.

### The paper correction, which was the user-facing part

Nobody owned those files, so I did them. Two pathspec commits, each verified
with `git show --stat`:

- `../axeyum-rado-paper` `proofs/README.md` -- the bullet "The Lean export has
  not been checked by real Lean. `lean`, `lake` and `elan` were absent on the
  machine that produced it" was **false in both halves** and is now the
  measurement, the 15/5/2 breakdown, the single root cause, and an explicit
  statement that this is a printer defect and **not** a kernel divergence,
  with nothing mathematical shown to be wrong. Also qualified the headline
  "0 `sorry` and 0 `axiom`" to "**by inspection of the source text**", because
  `#print axioms` has never executed.
- `docs/plan/next-actions-from-the-rado-paper-2026-08-12.md` -- A2 retired
  along with its premise.

Deliberately not touched: `docs/plan/lean-kernel-requirements-2026-08-13.md`
(the peer is correcting §2.1/R0.1 itself, and the file is modified by the codex
session -- doubly not mine).

**The lesson I keep relearning today.** Every one of the three corrections that
mattered came from someone re-measuring a thing I had already "verified".
The toolchain, the error count, the owner. Each time my evidence was real and
my *inference from it* was too fast.

## 22:xx — The guard that never existed. Best finding of the day.

The peer came back with the thing I should have looked for and did not: a
**defensive guard** documented at `lean_pp.rs:214-216` saying that only
non-parametric, non-indexed inductives are emitted as real `inductive`
commands, and that anything parametric or indexed "falls back to the axiom
rendering". `Eq` is parametric *and* indexed. Under that guard the rejected
export could not exist.

Their hypothesis was that the guard is bypassed via `real_inductives`, or that
its flatness test is wrong. I read `render_real_inductive` (`:409-441`) to find
out which. **Neither. It was never written.** The function carries the same
claim in a comment -- "Only flat (no params, no indices) inductives" -- and
then does no flatness test at all: fetch the `Declaration::Inductive`, write
`inductive {name}{uparams} : {render_lean(ty)} where`, append constructors,
return. The only two `None` paths are "not an `Inductive`" and "a constructor
name is not a `Constructor`". Neither concerns params or indices.

So: a guard existing only in prose, in two places, describing behaviour the
code does not have. That is the purest instance of this repository's own
signature failure mode I have seen -- and it is a **better finding than my
`num_params` one**, because `num_params` is the symptom and this is the
mechanism that was supposed to stop it.

### Why no amount of running the suites could have caught it

The real-Lean cross-check fixtures build their inductives as
`add_inductive(two, &[], 0, prop, ...)` -- zero params, zero indices, a flat
two-constructor enum. **Exactly the shape a working guard would admit.** The
corpus is structurally incapable of reaching the defect.

And it was **predicted in writing**:
`docs/prover-track/research/06-kernel-gap-analysis.md`, item 7, warns that
widening the corpus requires `lean_pp` to stop falling back to axiom rendering
for parametric/indexed families, "otherwise widening the corpus silently
widens the *vacuous* region." A realised prediction, not a hypothetical.

This is now the strongest argument for the NDJSON route over patching the
printer, and I have committed it as such: **the wire format carries
`numParams` natively and structurally cannot flatten the telescope**, whereas
a source printer can always regress into doing so -- and can do it while
carrying a comment saying it does not.

### Both halves of my asymmetry overstated, in opposite directions

The peer corrected the framing I asked them to check, and they were right on
both counts:

- **not** "Lean → axeyum works": five pinned single-root fixtures dual-admitted
  against official v4.30; L3 is 0/12; the dependency-closed population is
  unstarted; their own parity contract says the 5/5 total "is not complete K1
  authority";
- **not** "axeyum → Lean does not exist": `lean_pp.rs` is 1,690 lines and four
  suites feed rendered modules to a real Lean binary. The true statement is
  **"an export path exists, and the only non-trivial artifact ever put through
  official Lean is rejected."**

"Does not exist" invites "so build it". "Exists and is rejected" is worse and
truer. Adopted verbatim in the committed doc and passed to agent-d.

They also volunteered, unprompted, that their own §6.2:935-937 carries the
overclaim I had suspected -- "the infrastructure already exists and is
mutation-tested... K1 is 5/5", unqualified -- and are fixing it. Catching your
own load-bearing sentence before a referee does is worth more than the fix.

### Actions

- agent-d re-briefed: **audit the guard first**, before the telescope; decide
  deliberately between implementing the documented fallback and rendering
  params correctly; if the latter, change both comments, because they will
  then describe a guard that intentionally no longer exists.
- First required emitter regression, their suggestion: render the prelude's
  `Eq` and assert `numParams = 2`, `numIndices = 1` **on the wire**. One
  assertion that would have caught all of this.
- Committed the guard finding, the realised prediction, and the corrected
  framing to `docs/plan/lean-export-external-validation-2026-08-13.md`
  (link-check green, pathspec, one file).

## 22:xx — agent-a complete. 16 new values, conjecture survives 32/32.

Final: **32 cells decided from both sides, zero mismatches.** Ahmed-Schaal
Conjecture 2 (open since 2015) survives every test we could reach.

- 11 reproduce Ahmed-Schaal's published values -- all eleven, both sides, in
  **119 seconds**.
- 5 reproduce Song-Mao Table 3, plus their `s=3` row `S(3;3,3,8..14)`.
- **16 genuinely new**: (4,4,11)=120, (4,4,12)=131, (4,5,9)=125, (4,5,10)=139,
  (4,6,8)=135, (4,6,9)=152, (4,7,7)=139, (4,7,8)=159, (5,5,7)=132, (5,5,8)=151,
  (5,5,9)=170, (5,6,6)=137, (5,6,7)=160, (5,6,8)=183, (5,7,7)=188, (6,6,7)=202.

Committed `c0403d000` (trait extension, `offdiag.rs`, tests -- uniform encoding
byte-identical over 556,911 bytes of DIMACS, so the generalisation provably did
not disturb the existing families) plus three claim commits. Gates on HEAD: fmt
clean, clippy `-D warnings` clean, **73 tests**, ledger **59 claims / 0 errors**.

Unresolved and stated as such: `S(3;4,4,13)` (n=141 sat, n=142 running), and
the `s=3` bisections. 18 of 32 cells carry ledger entries; the rest have
verdicts and proofs on disk but no ledger packaging. A timeout recorded as a
timeout.

### The trap, now demonstrated rather than argued

`S(3;3,4,5)` at n=41 **is satisfiable**, and the stock symmetry-breaking
encoding calls it **`unsat`**. Every downstream tool would certify that
happily -- the proof would be a valid proof of the wrong formula. Four other
instances did not flip, so a negative control built on any of them would have
passed while testing nothing.

### Its three roadmap items, which I think are all right

1. **A satisfiability-preserving transform must carry its precondition in the
   interface.** `symmetry_blocks()` is the minimal version; the same principle
   belongs in `axeyum-rewrite`'s manifest contracts. A precondition in a doc
   comment is a wrong-`unsat` waiting for the first family that violates it.
   (Note how exactly this rhymes with the `lean_pp` guard that existed only in
   prose. Same disease, two crates.)
2. **Enumeration is the wall, and it is a modelling-layer problem.**
   `S(3;4,4,12)` spends 164 s generating 633,107,771 multisets to keep 451,622
   clauses, refuted in 0.1 s. Subsumption buys up to **1,402x** and is why we
   are past Song-Mao's frontier. There is no in-framework way to *size* an
   instance without materialising it.
3. **Novelty is part of a claim's meaning and nothing checks it.** Five claims
   shipped labelled NEW that had been published four months earlier; `prior_art`
   is narrative. Make novelty an enforced field. My audit caught it, but an
   audit is not a gate.

## 22:xx — batch 2 opens: van der Waerden

Slot freed, launching **agent-e** on B2-2. Chosen over the other queued items
because `w(2;3,t)` is **off-diagonal by nature** -- colour 1 forbids 3-term APs,
colour 2 forbids t-term APs -- so it consumes agent-a's per-colour extension
directly, on a second family in a different area of mathematics. That is the
cheapest available test of whether the generalisation was a real capability or
a one-target special case. Hosts s5/s6 inherited from agent-a.

## 22:xx — Verified agent-a's gates myself rather than taking the report

Ran `scripts/check-claim-certificates.py` independently:

```
59 claims re-checked, 0 errors, 13 row(s) not re-checked here
```

The headline matches agent-a's report. **The 13 is the interesting number**, and
it is not a failure: those rows' deciding CNFs and DRAT proofs are too large to
store in-tree, so the checker names each one and prints the exact command that
regenerates it, rather than passing it silently. That behaviour came out of the
previous session's fix ("the checkers now also report rows they could not
re-check rather than passing them silently"), and this is the first time I have
watched it work at scale on rows it genuinely cannot verify.

Worth stating precisely, because "59 claims, 0 errors" alone would overstate:
**46 rows were re-derived; 13 are regenerable-on-demand and were not.** That is
the honest form and it is what should reach any write-up.

Also visible in the log: the codex session is landing Lean work on the Rado side
-- `906a72cb1` "prove Nat order totality", `e83a8b7b1` "bound Rado witness in
sharpness branch", `ee0868eb1` "check Rado witness basic ranges". So the third
lane is formalising properties of the very witnesses agent-c is producing. Not
coordinated by me, and I should not assume it is aware of today's Rado results;
worth a note to that session once agent-c's values settle.

## 23:xx — "Are we actually fixing that unsat issue?" Three issues, two already closed.

Asked whether we are fixing the wrong-`unsat` problem. Checked each rather than
answering from memory, and there turn out to be three distinct things that have
been called that today:

1. **Off-diagonal symmetry breaking** -- **FIXED.** `c0403d000`:
   `symmetry_blocks` restricts colour-class ordering to genuinely
   interchangeable colours, with the control
   `whole_palette_symmetry_breaking_produces_a_wrong_unsat`
   (`crates/axeyum-search/tests/offdiag_schur.rs:111`) that fails on the
   unfixed code. A fix, not a demonstration.
2. **R1, `Evidence::check` returning `Ok(true)` for uncertified results** --
   **already FIXED, and I had been carrying it as open.** ADR-0384 made it
   three-valued: `Evidence::Unsat(None)` returns
   `EvidenceCheck::NothingToCheck`, and `is_verified()` is
   `matches!(self, Verified)` (`crates/axeyum-solver/src/evidence.rs:327-329,
   807-841`). So a bare uncertified `unsat` no longer passes the front door.
   This was the *highest* item on the Rado session roadmap. It is closed, and
   I should have checked before repeating it as an open concern.
3. **The general class** -- **NOT fixed, nobody assigned.**
   `RewriteRule.precondition` (`crates/axeyum-rewrite/src/lib.rs:144-145`) is a
   **`String`**, and `validate_rules` checks only that it is non-empty. Nothing
   ties the sentence to whether the rule may fire.

So the same pathology has now appeared three times in one day, in three crates:
a symmetry break sound only under an unstated condition, a "defensive guard"
that existed only in a comment, and a precondition that is a sentence. Two are
fixed; the third is the general form and is the one worth engineering.

### Launched agent-f. Fifth concurrent agent -- deviation flagged, not hidden.

Above the 2-3 guidance. Justified on two grounds: it is the soundness item, and
`crates/axeyum-rewrite/` is verified clean and unowned (`git status` empty), so
it adds no contention. Host s6.

Scope: **measure first** (which transformations are in the manifest and which
are deliberately outside it -- I counted 5 `RewriteRule {` constructions against
~20 `pub fn` entry points across 11 modules, and told it explicitly that **I am
not claiming that is a gap**, since `eliminate_arrays` is ADR-0010 and the
canonicalizer is ADR-0005; the question is whether the boundary is intentional
*and documented*). Then hunt for an actually violable precondition -- the
soundness payoff, and if found it outranks everything else. Then make
preconditions executable, with `symmetry_blocks()` as the reference: a
structured value the code consults, keeping the prose as documentation.

Told it the hardest-won detail from agent-a: **four of five instances did not
flip**, so a control chosen carelessly would have passed while testing nothing.
And a standing rule for its commits: if it finds a comment describing a check
the code does not perform, implement the check or change the comment in the
same commit -- do not leave a third instance of the pathology in the tree.

I keep having to correct myself in the same direction today: evidence real,
inference too fast. Item 2 is the clearest case -- I had been carrying a closed
P0 as open for hours because I never re-read the code.

## 23:xx — agent-a final. Verified again; and it audited its own conduct.

Resumed and finished. Verified the headline myself rather than taking it:

```
61 claims re-checked, 0 errors, 15 row(s) not re-checked here
```

Up from 59/13 when I last ran it, and the caveat holds its shape: the
not-re-checked rows are the ones whose deciding CNF or DRAT proof is too large
to store in-tree, each named with the exact command that regenerates it. The
honest form remains **46 re-derived, 15 regenerable-on-demand**.

Final mathematics: **32 cells, zero mismatches, 16 genuinely new values**;
Ahmed-Schaal Conjecture 2 survives everything we could reach. Unresolved and
stated exactly: `S(3;4,4,13)` (n=141 sat, n=142 never returned), the `s=3`
bisections, and `S(3;6,6,7)=202` decided but not yet ledger-packaged. 20 of 32
cells carry entries.

The nicest piece of work in it is not a value: their `S(3;3,3,12) = 94` breaks
an otherwise exact `9u - 13` progression, agent-a suspected a transcription
error, recomputed the row from scratch by bisection, and **confirmed 94**. The
break is real. Suspecting a published table and then checking it is the right
instinct; publishing the suspicion without checking would have been the worst
possible move.

### It audited its own conduct, unprompted, and found the same disease again

Two defects in its own tooling, both recorded in its FEEDBACK:

1. a lane that **exited 0 having done nothing** -- wrong binary path, no `if`;
2. the tally it added *to prevent a recurrence* printed `made=4 of 3`, because
   `set --` inside the loop clobbers `$#`.

I reproduced the second mechanism directly (`set -- a b c; for ...; do set --
"$@" x; done` prints `made=6 of 3`). So the fix for a green-gate-over-nothing
was itself a green gate over nothing. That is the fourth instance of the same
pathology today, and the first one where the *remedy* carried it.

Running tally of the pathology, one day, four crates:

| where | form |
|---|---|
| `axeyum-search` symmetry breaking | soundness condition unstated in the interface -> wrong `unsat` |
| `axeyum-lean-kernel` `lean_pp` | "defensive guard" documented, never implemented |
| `axeyum-rewrite` manifest | precondition is a `String`, presence-checked only |
| agent-a's own harness | gate exits 0 having run nothing; its remedy miscounts |

agent-f is on the third. The fourth is a reminder that the discipline is not a
property of the codebase -- it has to be re-earned by every script anyone writes,
including the ones written to enforce it.

## 00:xx — Two headline results, and my Lean framing was wrong in BOTH directions

### agent-b: `R_4(5(x-y)=4z) = 741`. The repository's standing open claim is closed.

Both sides machine-checked. Lower: a 4-colouring of `[740]` replayed by an
`O(n^2)` enumerator sharing no code with the encoder. Upper: a **complete
adaptive cube cover** of `F_741` -- **6241 cubes, every one refuted, every DRAT
proof checked by axeyum's own backward checker.** No external solver, no
external checker, anywhere.

The construction predicted 741 exactly (`5^4 + 5^3 - 2*5 + 1`) and the
prediction held. Contrast with the k=5 prediction that agent-c refuted this
morning: the same machinery produced a confirmed prediction and a refuted one in
one day, which is the best possible evidence that it is not merely agreeing with
us.

It has **not committed the claim yet** -- `rado_replay_tree_cover` is
re-deriving all 6241 refutations from the merged ledger alone, `strict_steps=1`,
~52 minutes -- on the stated grounds that it would rather find a disagreement
before the claim exists than after. Correct instinct.

### agent-d: Lean's own kernel now accepts the axeyum Rado development

The seam I called S1 is closed, and four things landed:

1. **The module typechecks. `EXIT=0`, 0.138 s**, down from `EXIT=1`, 22
   diagnostics. And **`#print axioms shell_closed_form` executed for the first
   time**: *"does not depend on any axioms."* Before, the cascade meant the
   theorem was never declared and the command could not find its subject.
   Non-vacuity proved, not assumed: mutating the theorem *statement* gives
   `EXIT=1`, "Type mismatch".
2. **My "axeyum to Lean is broken" was too pessimistic.** With
   `AXEYUM_REQUIRE_LEAN=1` so a missing binary fails rather than skips: 39
   tests, 0 failures, and `lean_crosscheck --ignored` reports **163 of 163
   modules across 70 families**, four of them tamper controls where real Lean
   *rejects* a mutated module. Vacuity control run: `AXEYUM_LEAN_BIN=/nonexistent/lean`
   makes the suite FAIL. The accurate statement: *an export path exists and is
   exercised on 163 modules; the one shape it could not express was a
   parametric or indexed inductive rendered as a real `inductive`, which only
   the Rado module used.*
3. **The `lean4export` NDJSON emitter exists** (`lean_export.rs`), and all **17**
   committed official v4.30 fixtures import, re-emit and re-import with matching
   ADR-0350 identity manifests. Emitter and importer share no code. It also
   mutation-tested what the round trip does *not* prove rather than asserting
   its strength.
4. **External acceptance RUNS -- it was reachable with the pinned toolchain
   alone.** `import Lean` from a bare `lean --run`, `mkEmptyEnvironment` +
   `Lean.Environment.addDeclCore`: no lake project, no network, no third-party
   checker, no `lean4export` install. All 17 fixtures accepted, and **the axeyum
   Rado development accepted: 3,854 records, 74 declarations, 10 inductive
   groups, 97 constants, 0.9 s, EXIT=0** -- from an **empty** environment, so
   nothing is satisfied by Lean's `Init`, and the quotient package comes from
   our stream so the double-add trap cannot arise. Constructors and recursors
   are deliberately not replayed: Lean regenerates them, which is *stronger*,
   because later declarations mentioning our exported recursor must then check
   against Lean's own.

   Tamper control, and this is the sentence of the day: given another theorem's
   closed well-typed proof, **Lean's kernel restates our theorem and refuses**
   -- `(kernel) declaration type mismatch, 'rado.shell_closed_form' has type ...
   but it is expected to have type ...`, EXIT=1. Now a gate
   (`tests/real_lean_kernel_replay.rs`).

**So the F-C3 comparison resolves in our favour, measurably.** Li reaches Lean
through `axiom lem_keypair_sat`, justified by a doc comment. We now hand Lean's
own kernel the actual declarations and it accepts them, with a control proving
it would reject a wrong one. That is the difference between asserting a SAT
result to a proof assistant and having one check it.

I was wrong in both directions and should record how: I called the outward path
"broken" when 163 modules already crossed it, and I called external acceptance
a research project when it was two Lean API calls away. Both errors came from
generalising a single measurement -- one artifact failing -- into a statement
about a capability.

## 00:xx — agent-a again: 45 cells, 18 new, and an exit 137 correctly refused

**45 cells decided, 27 published values reproduced, 18 new, no mismatch
anywhere.** New since the last report: `S(3;4,4,13) = 142`,
`S(3;4,5,11) = 153`, and the whole `s=3` bisection lane -- 11 cells, 11
agreements with Song-Mao Table 3 (`S(3;3,3,8..14)` and `S(3;3,4,8..11)`).

Both anomalies it chased are now settled as **real**: the `(3,3,12) = 94` break
in the otherwise exact `9u - 13` progression, and the `(3,4,u)` row's ragged
11/8/12 steps. Neither row follows a linear formula, and that is now known
rather than suspected. Twenty-seven independent reproductions of other people's
published values, zero disagreements, is a stronger statement about our encoder
than any of the new values.

### The OOM, and why its shape matters more than the cell

`S(3;3,3,15)` was OOM-killed and is recorded as unresolved, not as a result:

```
  n=100: sat (48308 clauses), witness replayed
  s3-rows.sh: line 7: 373026 Killed   timeout 3600 ... threshold 3 3 15 100 150
  rc=137 -- see above, NOT a verdict
```

Song-Mao report 122; **we neither confirm nor contradict it.**

The shape is the finding. `threshold` mode confirms both bracket ends before
bisecting, so the kill landed on the *upper* probe while enumerating `L(15)`
solutions on a 26 GiB host. The raw transcript therefore reads "sat at 100,
then nothing" -- anyone reconstructing the row from `THRESHOLD` lines alone
sees a **silent gap, not a failure**. The `rc=137` annotation is the only thing
distinguishing "the machine ran out of memory" from "the lane moved on".

That is the exit-137-reads-like-a-refutation trap met in its natural habitat,
and it is subtler than the version in the brief: the danger is not that a kill
is misread as `unsat`, it is that a kill leaves *no row at all* and the absence
looks like a decision not to run. Recording a negative is not enough; the
negative has to appear where a reader would look for the positive.

### The gap worth closing

**20 of 45 decided cells are packaged.** Twenty-five have verdicts and proofs
on disk and no ledger entry -- which is precisely the difference between "we
computed this" and "the system can re-derive it on demand". Resuming agent-a on
packaging rather than on new cells.

## 00:xx — Check-in: an operational hazard nobody owns

### s0's `/tmp` is a tmpfs and it is eating the RAM the checks need

```
s0  total 123  used 67  free 15  shared 44  available 55
    /tmp: tmpfs 62G, 50G used, 13G free
```

`/tmp` on s0 is **tmpfs**, so its 50 GiB are RAM. Available has fallen from the
68 GiB agent-c planned its `(5,3,4)` check against to **55 GiB**, and about
**13 GiB of it is stale `decbench-*` / `glaurung-*` directories dated
2026-08-08** -- a different project, five days old. I am not deleting another
project's files; surfaced to the user instead.

At agent-c's measured **6.6x** blow-up from proof bytes to resident memory,
that headroom is right at the edge for an 8.4 GB certificate. Warned it, and
pointed it at s4 (62 GiB of free tmpfs, ~119 GiB available) as the only host
that can carry a large check -- s5/s6/s7 have 14 GiB tmpfs and ~26 GiB RAM and
cannot.

This is a new entry in the *tools lie* register and a fresh one: **the resource
a job needs was being consumed by an unrelated project's leftovers, through a
filesystem that does not look like memory.** `df` says disk; `free` says
`shared`. Neither view alone tells you an OOM is coming.

### agent-b: the satisfiable side closed too, and a cross-toolchain check

All 60 SLS jobs finished `not-found` -- five start distributions (the `[740]`
witness with each of the four colours appended, plus a cold round-robin), twelve
seeds, 25M moves each, 4101 s. Corroboration only; the cover is the proof. But
it is the fourth independent thing pointing the same way.

Then a nice touch: the second replay of the merged ledger runs on s7 with a
**different rustc** (1.93.1 stable against s4's 1.99.0-nightly), so the
step-count comparison becomes a **cross-toolchain determinism check** rather
than merely a cross-host one. Determinism is a public API promise in this
project; that is the first time today anyone has actually tested it across
compilers.

### agent-c: the capability the tree lacked

A `check` subcommand that regenerates the formula from `(a,b,k,n)` and
re-derives a **stored** proof without re-solving. Nothing in the tree could do
this: `solve` bundles production with checking, and `recertify_rado` always
re-solves first (`recertify_rado.rs:136`). Saved 113 minutes on one instance --
but the real point is that a certificate becomes **movable between machines**,
which turns the memory asymmetry from a nuisance into a scheduling parameter.
A pipeline that cannot move a certificate re-derives it every time the
constraint bites.

### agent-d: two operational notes worth propagating

- The shared scratchpad hit `EDQUOT` mid-build, and cargo reported it in a way
  that **looks like a compiler error**. Four agents' `target/` directories on
  one 62 GiB tmpfs.
- Its snapshot copy of `lean_pp.rs` and the live worktree copy diverged by a
  helper-function extraction between its two commits. Semantically identical
  and HEAD carries the tested version -- but the lesson is exact: **"copy from
  snapshot, then commit" needs a diff check, not a copy**, when the worktree is
  shared. Campaign rule 7 gave isolation for *building* and I did not think
  through what it means for *committing*.

### agent-e: the prior art it found

Its diary notes that the one existing certification of this value needed
**3,627 cubes of cube-and-conquer, per-cube LRAT, and a Lean reflection pass**;
ours is one process, one 20-second solve, and our own backward checker. Also
that `W(4,3) = 76` failed on the **lower** side -- finding a 4-colouring of
`[75]` exhausted the CDCL budget in 44 s -- the mirror image of agent-a's
finding that CDCL beat SLS everywhere. The two sides of a threshold are
different problems and want different engines; its driver now lets them.

## 01:xx — agent-d complete. The loop is closed, and my third wrong inference.

Verified independently before writing anything:

```
$ cargo test -p axeyum-lean-kernel --test real_lean_kernel_replay
the_real_lean_kernel_accepts_an_axeyum_development_and_rejects_a_tampered_one ... ok
1 passed; 0 failed   (2.44s)
```

### The fourth defect refutes a conclusion I committed to a document

I wrote that repairing the three known defects "still fails, because the
elaborator reaches for `CoeFun`", and inferred that **surface syntax is
structurally hostage to elaboration**. Wrong. There was a fourth *printer*
defect: Lean inserts a constant's pending implicit arguments as soon as a
**parenthesized** application closes, so `(@Eq.refl α) a` fails where the flat
`@Eq.refl α a` checks. The writer emitted nested spines `((f a) b)`. Flat
spines fixed it.

`lean shell_closed_form.lean` → **EXIT=0, 0.138 s**, and `#print axioms` runs
for the first time: *"does not depend on any axioms."* Non-vacuity measured:
mutating the statement gives EXIT=1.

Three times today I turned a sound measurement into a wrong claim about a
capability:

| I wrote | actually |
|---|---|
| "the toolchain is absent (verified)" (inherited, repeated) | installed and pinned; `which` measured `PATH` |
| "axeyum → Lean is broken / does not exist" | 163 modules, 70 families, already cross-checked |
| "surface syntax is hostage to the elaborator" | a fourth printer bug; flat spines fixed it |

The evidence was sound every time. The generalisation was not. Stated as a rule
I can actually apply: **an unexplained failure is evidence about one artifact,
and becomes evidence about a capability only once its mechanism is understood.**
`CoeFun` was a symptom I could not explain and I promoted it to a law.

### What agent-d also found that I would not have

- Round-trip **blind spots measured, not assumed**: mutating `numIndices` fails
  6 of 7 tests, but mutating the derived `k` flag fails only **2 of 7**, because
  the importer treats `k`/`isReflexive` as descriptive. It then compared those
  fields against Lean's own bytes across 71 families and 75 recursors — and
  found a **real `isReflexive` defect** that only that comparison could catch.
  Byte identity: 0 of 17, structurally. A round trip that had been asserted to
  be strong was instead characterised.
- Frozen `(len, fnv1a)` render pins are the wrong instrument: a legitimate
  printer improvement moved all four and reported two opaque integers.

### The clobber my own rule caused

Commit `c33553e72` repairs a collision in which agent-d's snapshot copy-back
**silently reverted the codex lane's `a10f12912` refactor**. Campaign rule 7
("build from your own `git archive HEAD` snapshot") gave isolation for
*building* and I never thought through what it means for *committing*. Copying
a whole file back over a shared worktree discards whatever landed meanwhile.

**Rule 7 needs a second half: commit by diff, never by copy.** Recorded, and it
is my error, not agent-d's — it followed the rule I wrote.

### Documents corrected

- `../axeyum-rado-paper/proofs/README.md` — this morning I made it say the
  export is *rejected*; that is now false in the opposite direction. Rewritten:
  the module typechecks, `#print axioms` establishes the `0 axiom` property by
  kernel rather than by inspection, and Lean's own kernel accepts the
  development with a tamper control. Committed.
- `docs/plan/lean-export-external-validation-2026-08-13.md` — appended the
  resolution and the table of my three wrong inferences, then **retitled it**,
  because the file was called "The Lean export is not externally checkable yet"
  and ends with Lean accepting it. Corrections are appended rather than edited
  in, so the sequence stays legible.

## 02:xx — agent-f complete, and `main` was red. Both halves now traced.

### agent-f: a negative result, honestly bounded

**No violable precondition found among the 57 manifest rules** -- and the
search is described, which is the only thing that makes a negative worth
having: the guard live across `axeyum-solver --lib --features full`
(1121/0), a new 4096-term sweep committing **11,972 checked applications,
11,972 denotation-checked, 0 coverage holes**, a second independent judge
replaying 163,840 further comparisons, and degenerate arguments generated
deliberately per the `a946f925` rule.

**My brief was wrong about the manifest's size.** I counted 5 `RewriteRule {`
struct literals; there are **57 rules**, built through a helper
`fn rule(id, name, precondition)` at `canonical.rs:622`. Worse for the original
point and better for the finding: all 57 hard-code the same
preservation/projection/tests/enabled fields, so **the prose `precondition`
string was the only per-rule field carrying applicability, and the only field
nothing read**.

Default-on in release was decided by measurement rather than argument: 21.51 s
against 21.55 s end to end, verdicts bit-identical, 2.2x on canonicalisation
alone which is ~0.2% of solve time. It had planned a `debug_assertions` gate
and dropped it on the numbers.

Its scope finding is worth acting on: three documents disagree about what the
manifest governs (`axeyum-rewrite/README.md:8-11` and
`docs/internals/rewriting.md:27-36`, both incomplete; **contradicted** by
`docs/contributor-guide/adding-a-rewrite.md:38-39`; **asserted away** by
ADR-0005's Consequences at `:83-87`), and two disjoint registries exist
(`RewriteManifest` vs `TrustId`/ADR-0031) with nothing saying which a new
transform joins.

### `main` was red, and neither failure was where it looked

**Half one, seven tests: `reconstruct::tests::*_family_generated_source_is_byte_stable`.**
agent-d's flat-spine printer fix legitimately moved generated source for seven
families; it updated four pins and these seven were not in that set. So a
*correct* fix turned `main` red because the test encoded an assumption about
output that nothing tied to a reason -- the fourth distinct form of today's
pathology, and the one that bit hardest, since `(1203, 9126266555841633607)`
against `(921, 17229612914579886985)` gives a reader nothing to decide with.
Resumed agent-d, told it not to paste in new numbers but to establish
correctness per family first (it has the instrument: `lean_crosscheck` is
163/163 before and after) and then to replace the instrument per its own F-D4.

**Half two was mine, and the gate was right.**
`stored_ledger_cnf_artifacts_regenerate_byte_identically` failed with

```
claim id "rado-r4-a5-b4-frontier" carries 1 CNF artifact(s) but does not parse
as rado-r<k>-a<a>-b<b>, so its instances were never checked
```

`parse_claim_id` split on `-b` and parsed the remainder whole, so a trailing
qualifier broke it. The gate **refused to pass artifacts it could not verify**
rather than skipping them -- exactly the discipline the previous session built
in, firing correctly on new data.

Fixed in `crates/axeyum-cnf/tests/colouring_encoding_parity.rs`: `b` is the
leading digit run, any remainder must be a `-`-separated word, and ids not of
this shape still fail closed and are still reported. Kept the crate's
deliberate no-JSON-dependency design (the comment at `:231` says so) rather
than reaching for `claim.json`.

**The payoff is not the green gate.** `F_741` -- the deciding instance of
`R_4(5(x-y)=4z) = 741` -- and `F_243` were being carried by the ledger and
verified by nothing. They now regenerate byte-identically against the encoder.
A parser that could not read two ids had quietly removed the campaign's two
most important instances from the only gate that checks them.

Also noted from agent-f: three link steps died with
`ld terminated with signal 7 [Bus error]` because `/tmp` is a 62 GiB tmpfs at
80%. **That reads as a compile error and is not one** -- the same shape as the
`EDQUOT` that looked like a cargo failure. Campaign rule 7 should name a
disk-backed scratch path, not just "your own snapshot".

## 03:xx — agent-a packaging complete. Verified, with one caveat I found.

Verified independently: **`89 claims re-checked, 0 errors, 19 row(s) not
re-checked here`**. All 48 decided cells packaged, up from 20.

### Novelty is now a field -- on 48 of 89 claims

Distribution measured directly from the ledger:

```
reproduction 30 | new 18 | (absent) 41
```

`check_novelty` is a **documented soft rollout**: `if novelty is None: return
[]`, and the docstring says so plainly -- "Claims that predate the field are
not failed for lacking it; a claim that HAS it must have it right." That is an
honest, defensible migration and it is written down.

But it means the field covers **48 of 89 claims (54%)**, and the uncovered 41
are the *Rado* claims -- including the campaign's most-cited values: `741`,
`226`, `313`, `625`. From outside, "novelty is an enforced field" reads as
coverage; the reality is coverage of the newest family only.

**Backfilling the 41 is a real action item**, and the material exists: agent-c's
Table 10 census is exactly the classification needed (12 exact published cells,
7 blank, `(2,3)` the bare `> 225`), and Li's artifact repo settles the `b=1`
column. Then make the field required and delete the `None` escape. I am not
doing it by hand across 41 claims tonight -- it is literature classification,
not data entry, and getting it wrong would be worse than not having it.

Where the enforcement *is* live it is properly built: three negative fixtures
confirm rejection of an unknown label, a `reproduction` with empty `prior_art`,
and a `reproduction` whose citations are **adjacent but not supporting** (no
cited row establishes the claimed value). The generator also asserts each
reproduced value against the published one *before writing*, so a divergence
fails at generation rather than becoming a quiet claim contradicting the
literature.

### agent-a corrected its own published cause

It wrote up an OOM as `to_dimacs()` doubling memory, then found the decide run
for the same cell had printed **`peakRSS=15297660kB` into its own log**. The
cost is the `L(13)` enumeration; bundling fails because it runs two 15 GB
phases in one address space. It published a cause before reading a number it
already had.

What caught it is the part worth keeping: **putting the number in RESULT.md
next to the claim, where the two visibly disagreed.** That is a cheap general
technique -- co-locate the measurement with the assertion it supports and
contradictions become visually obvious.

### The silent-gap requirement, now stated properly

FEEDBACK item 8: **every producer emits a row per requested item, including
ones it could not decide, in the same shape as a success.** `harness.rs`'s
`PendingReason` is the existing pattern to copy.

And a near-controlled experiment for it: the same stale-binary bug hit three
times, and the only variable that mattered was whether the producer counted.
Once it printed `COMPLETE` / exit 0 with three cells missing; twice it printed
`made=0 failed=14 of 14` and was caught in seconds.

### Lanes stopped, recorded exactly

`S(3;4,4,14)` (n=152 probe killed at 7m33s/3.3 GB), `S(3;3,5,10)` (bisection
killed, n=90 sat confirmed), `S(3;3,3,15)` (OOM, exit 137). **No verdict on any
of the three.** Song-Mao report 122 for the last; we neither confirm nor
contradict. Both hosts verified idle.

Headline preserved: **30 independent reproductions, zero disagreements**, and
both published-table anomalies resolved as real.

## 03:xx — PIVOT: from values to the framework

User direction: **focus on fixing and improving axeyum, not chasing micro-papers.**
Acting on it immediately.

Honest reading of why this is right, from my own analysis an hour earlier:
agent-a's 18 new values were **predicted in advance and confirmed** --
`S(3;4,4,u)` is exactly `11u-1` for u=4..13, which is `stu-tu-u-1` at `s=t=4`,
a straight line the published conjecture already specifies. 48 cells, zero
mismatches, **zero surprises**. The one outcome that would have been real
mathematics -- a counterexample to an open conjecture -- did not occur, and
confirming a conjecture on more instances does not move it toward proof. That
was my brief's fault: I chose cells that tested a conjecture nobody doubted
rather than the boundary where it might break. agent-c's k=5 refutation was the
campaign's only genuine surprise precisely because its prediction *could* fail.

### Wound down, with instructions to collect rather than discard

- **agent-b (741):** finish the 6241-cube replay and land the claim; the
  cross-toolchain determinism check (rustc 1.93.1 vs 1.99.0-nightly) is worth
  completing either way. Then write the **route A for tree covers** design and
  the **branch-point selection** heuristic -- both are on the roadmap and it is
  the only one who can specify them.
- **agent-c (`a^k`):** finish only what is mid-flight, start nothing new,
  package, and spend real effort on F-C7/F-C10 (the 6.6x measurement and
  certificate mobility) and F-C2/F-C5 -- someone else will implement those and
  its diary is the specification.
- **agent-e (vdW):** drop `w(2;3,20)` entirely. Keep the part that was always
  the point: **did agent-a's per-colour extension carry to a second family in a
  different area of mathematics, unmodified?** That answer is worth more than
  any van der Waerden number and only it can give it. Plus one certified value
  as the end-to-end demonstration, and the SLS-vs-CDCL route guidance.
- **agent-d:** unchanged, it is already engineering (render pins).

### Launched agent-g on the item that limits everything else

`axeyum-cnf` memory ceiling. Three parts, ordered so the cheap safety win lands
first:

- **G1** -- predict and refuse. Compute expected resident cost from proof size,
  compare to available memory, decline with a typed error and report the
  observed ratio. This alone removes the exit-137-reads-like-a-refutation trap
  and makes checks schedulable. Land separately.
- **G2** -- file-backed backward DRAT checking. ADR-0381 did the **producer**
  half (22.3 GiB -> 1.9 GiB); the **consumer** half was never done, and that
  asymmetry is the whole problem: *we can produce proofs we cannot check.*
  Differential test against the in-memory checker built **first**; a
  disagreement is a P0 and the headline.
- **G3** -- `CnfFormula` flat arena. 2.3 GB RSS for 330 MB of literals, ~7x
  from per-clause allocation. Compounds with G2: every byte saved is headroom.

Gave it s6 deliberately as a **negative control** -- it is the host that
currently fails -- and told it to keep its build off `/tmp`, since tmpfs
consumption *is* the memory it is trying to measure. That trap has now produced
a bus error, an EDQUOT that looked like a compiler error, and a silent
reduction in the headroom agent-c scheduled against.

Next engineering lanes queued as slots free: `axeyum-search` consolidation
(front door + `check` + `known_witness`, collapse the duplicate colouring
encoders and make the cited-but-absent parity gate real, `run_cover` defects,
instance sizing), and model-reconstruction routes for the rewrite passes that
introduce fresh symbols.

## 04:xx — Green, and `741` is in the ledger. Both verified here.

```
$ cargo test -p axeyum-solver --lib --features full
1121 passed; 0 failed          29.17s

$ python3 scripts/check-claim-certificates.py
99 claims re-checked, 0 errors, 19 row(s) not re-checked here
```

`rado-r4-a5-b4-frontier` is now `epistemic_status: computed`, titled
`R_4(5(x-y)=4z) = 741`, carrying three **checked** evidence rows:
`instance-pin`, `witness-replay`, `cube-tree-cover`. The repository's standing
open claim is closed and re-derivable.

### agent-d did the thing I asked for and it falsified its own draft

Told not to paste new numbers into the render pins, it built an **A/B with
`lean_pp.rs` as the only variable** (pre-change `0535af82a` against HEAD), four
independent checks:

- **control** -- restore the old printer and all seven pins pass, so the pins
  are a pure function of the printer and nothing else moved;
- **content** -- all 15 modules identical after normalising parentheses and `@`;
- **semantics** -- real Lean accepts all 15 old and all 15 new and returns
  **byte-identical `#print axioms` output for every old/new pair**;
- **corpus** -- `lean_crosscheck --ignored` 163/163 before and after.

And the payoff: **the A/B falsified what it would otherwise have written.** Not
"only parentheses" -- four datatype modules also gained `@` on constructors,
because that family is the only one emitting real Lean `inductive`s and Lean
makes an inductive's parameters implicit in its constructors. The same fact that
made the Rado module check. A claim that would have been wrong, caught by the
instrument built to justify the claim.

The replacement instrument is right: fixtures diffed as text with the first
differing line and a bless command, so a printer change is *reviewable*; all 15
run through real Lean; `#print axioms` confirmed to execute; no `sorryAx`; and a
negative control that swaps one assumed hypothesis for another **inside the
proof term**, with hypothesis names read out of the fixture so re-blessing
cannot quietly turn the control into a no-op.

### Two corrections, one of them mine

**agent-d's miss was the documented gate.** CLAUDE.md names
`-p axeyum-solver --lib --features full` for solver changes and explains that a
wrong-unsat once shipped exactly that way. It ran the eight Lean suites, the
163-module corpus, both Lean crates, clippy and rustdoc -- and skipped that one,
because it had classified its work as a lean-kernel change. **`lean_pp` output
is solver-visible; the classification was the error.** Worth generalising: the
gate list is indexed by crate, and the blast radius is not.

**I misattributed a commit.** I repeated agent-f's attribution of `5f07145e1` to
agent-d's lane; it is the R1/R2 lane's *prove Nat order antisymmetry*. The root
cause is structural: **every commit in this checkout carries the same git
author, so lane attribution from `git log` is not recoverable.** Two lanes got
this wrong tonight and so did I.

### Campaign rules 7-10, rewritten from tonight's failures

7 amended (snapshot **on disk**, not `/tmp` -- tmpfs is RAM and has now caused a
bus error, an EDQUOT that read as a compiler error, and a silent cut to a lane's
scheduled headroom); 8 **commit by diff, never by copy**; 9 **shared append
points are not protected by pathspecs** -- and the session protocol *tells*
every lane to edit `PLAN.md`; 10 **tag commits with an `Agent:` trailer**.

### One inconsistency left standing, small but the same disease

The claim id is `rado-r4-a5-b4-**frontier**` while its status is now `computed`.
The id encodes a status that has changed -- the same "id as a data channel"
problem that made the parity gate skip this exact artifact six hours ago. Not
worth a rename tonight (ids are referenced from artifacts and prose), but it
belongs on the list: **status lives in a field, never in a name.**

## 05:xx — agent-e complete. The capability question is answered, and my brief was wrong again.

### The answer the lane existed for

**agent-a's per-colour extension is a capability, not a special case.** Van der
Waerden -- a different area of mathematics, a different defining relation, an
inverted cost profile -- consumed it with **78 lines of additive change** (2 in
`lib.rs`, 76 in `family.rs` for spec parsing) and **zero** changes to the
encoder, CDCL core, DRAT sink, backward checker, cover harness, ledger or local
search. The single edit to pre-existing behaviour was one line of a test that
had used `vdw` as its example of an *unknown* family.

The sharpest evidence was accidental: agent-a's driver is written against the
concrete `OffDiagonalSchur`; agent-e's is written against
**`Box<dyn ColouringFamily>` + `parse_family(spec)`**, so one binary drives
`W(4,3)`, `W(2,5)`, `w(2;3,20)` and every Rado/Schur instance without
recompiling. That is the generalisation being real rather than asserted.

### 13 certified values, and a claim worth checking

`W(2,3)=9`, `W(3,3)=27`, `W(2,4)=35`, **`W(2,5)=178`**, and `w(2;3,t)` for
`t=4..12` -- both sides, pure Rust, no external solver or checker.

`W(2,5)=178`: 2,153,837 DRAT steps, solve 20.05 s + check 22.19 s, **43 s end
to end in one process.** The only prior machine-checked certification of that
value needed 3,627 cubes, per-cube LRAT, LRAT-Catcher composition and a Lean
reflection pass across six tools. agent-e's stronger claim -- that **no
classical van der Waerden number carries a machine-checked UNSAT proof in the
peer-reviewed record** -- is the one to verify before it goes anywhere near a
paper.

### My brief was wrong about the target

I sent it after `w(2;3,20) = 389` as "open since 2011". It is **not open**: 389
is a *certified* lower bound printed in AKS Appendix A.1, and probably exact
since Kouril 2015. Genuinely open starts at `t >= 21`. Third brief error of the
campaign, and the same shape as the others -- I read a summary and did not read
the appendix.

Its census, killed on my instruction, is worth keeping: depth-6 split gives
**identical** results at `n=388` and `n=389` (14 refuted, 9 open, 41 unreached),
so depth 6 cannot see the boundary at all. A negative result about the method,
not the number.

### Two measurements that correct campaign folklore

- **Subsumption gives exactly 1.000 on van der Waerden**, measured. Every
  length-`k` progression has exactly `k` points and no two nest, so the
  antichain is the whole set. agent-a's 1,402x reduction is family-specific,
  not a general lever. *Enumeration is free here; the proof is the wall.*
- **Engine selection inverted between lanes.** agent-a: CDCL beats SLS by three
  orders of magnitude. agent-e: on 4-colour `W(4,3)`, CDCL **cannot find the
  satisfiable side** -- it defeated a 44 s CDCL budget, 14 SLS lanes over 35
  minutes, 4.0e9 DFS nodes and a cover. The unsat side is a propagation problem,
  the sat side is a search problem, and **the gap widens with colour count.**
  That belongs in the framework as a declared `sat_side_engine` plus an
  untrusted `known_witness` inlet, not as folklore in two diaries.

Its item 1 is the same wall agent-g is on, found independently from the other
side: `check_drat_backward` takes a **slice**, so `parse_drat` must materialise
everything. `w(2;3,13)` died with a 6.0 GB proof after refuting **247 of 256
cells**, each re-derived. Two lanes, two families, one constraint.

### It fixed three gates that were reporting success over work they were not doing

And this is the important operational finding: `novelty` was missing from the
schema and validator, so **62 claims failed on a single message that masked 228
real errors underneath**. Also `classify_payload` sniffing colouring-text from
the whole file rather than the comment-stripped body (61 witnesses, including
*all* of agent-a's, failing their own format contract), and `check_status:
not-checked` rows being skipped in silence.

Verified here after its repairs: certificate checker **`102 claims, 0 errors`**;
validator **`102 claims, 228 errors`**. The 228 are real and are agent-a's
claims -- generator path with a parenthetical symbol tested as a path, refs
asserted `resolved: true` with **no `graph_pin`**, and stray `F_*.cnf.gz` files
that no evidence row names. Resumed agent-a to fix them; two of the four shapes
need the author's judgement, not mine.

**A masked gate is worse than a red one.** This one shipped green over 228
defects for the entire campaign.

## 05:xx — agent-a asked for sign-off on editing another lane's repaired gate. Approved, after checking.

It found that `validate-claims.py`'s `ARTIFACT_FORMATS` has no `dimacs-cnf-gzip`,
so a gzipped deciding instance cannot be pinned at all -- and it declined to
edit the gate without asking, on the grounds that agent-e had just repaired it.
Correct instinct.

I verified its three claims rather than taking them:

- the vocabulary's own comment reads *"deliberately names only formats this
  ledger actually stores"*, and the ledger now stores gzipped DIMACS, so the
  addition **follows** the policy;
- `drat-text-gzip` and `drat-binary-gzip` already exist, with a deliberate
  comment about the gzip envelope -- the pattern is established;
- `detect_artifact_format` returns `fmt + envelope`, so the sniffer **already
  emits `dimacs-cnf-gzip`** for a format the vocabulary then rejects as
  unknown.

So the gate is internally inconsistent and agent-a found it. Approving is not
loosening: rule 1 still requires the declared format to match the **bytes**, and
32 deciding instances move from unexplained-or-deleted to hash-pinned and
format-verified. Its alternatives were measured, which is why the argument was
easy to accept -- 155.3 MB uncompressed against 23.7 MB in a 224 MB directory,
or deleting the CNFs and losing the clause-wise validation that catches this
family's characteristic wrong-unsat.

Conditions: keep it out of the checker-consumable vocabulary (a deciding
instance is not a proof, and conflating them is the B8 defect again); negative
controls **both ways**, demonstrated failing; and record in the diary that it
edited a gate another lane had just repaired, so any disagreement stays legible.

### The best decision anyone made today

agent-a refused to mark `C:schur-number` resolved until the concept node is
actually committed, and said why: *"Marking it resolved against a pin that does
not contain it is precisely the stale-resolution defect you chased yesterday; I
am not creating a second instance of it to save a round trip."*

That is the discipline operating unprompted and against its own convenience,
and it is a better outcome than the fix I was chasing. It also verified the
concept files exist **at the exact pinned commit** rather than in the working
tree -- the method I failed to use when I published `a29a9e2a...` as a dangling
pin. It independently confirmed the pin is an ancestor of HEAD.

I will review and commit `graph/concepts/schur-number.md` in `../math-education`
myself, then it flips the 48 flags and re-pins in one pass.

## 06:xx — agent-h complete. My brief pointed at the wrong ceiling.

### Brief error #4, and it is the exact failure this repository documents

I sent agent-h at `DP_POOL_BUDGET` on the strength of an error message reading
*"Davis-Putnam working set exceeded ... (proof too large for inlined resolution
reconstruction)"*. **That guard never fires.** It protects the *third* fallback
in `reconstruct_resolution_step`; LRAT hint chains from our own pipeline take
`reconstruct_ordered_rup_step` instead, and across 22 Rado instances from 85 to
4,572,930 hints the Davis-Putnam path was **never entered**.

agent-h's line is the right summary: *"a lane sent at that budget would have
spent its session on a guard that does not fire."*

CLAUDE.md's Gotchas literally lists this shape -- "an error message naming a
node cap when the real cause was an i128 overflow". I read a message, not a
measurement, and briefed from it. Fourth brief error of the campaign.

The real bound is the **kernel expression arena**: ~90-100 bytes RSS per
interned node, ~190-460 nodes per LRAT hint. Answer (c) from the brief -- the
algorithm is fine, its *materialisation* is bounded. `F_45` at 4.57M hints ran
35 minutes to 4.1 GB with no result; the slope puts it near 150 GB.

### What landed

`reconstruct_resolution_proof_compact`: backward slice + CPS clause encoding +
one closed `Declaration::Theorem` per live clause. **5.6x fewer arena nodes,
55x faster at n=141, and the ratios are still rising with size.** All three
mechanisms already existed for the bit-blast lane and had never been wired to
the clausal front door -- so the fix was integration, not invention.

A correction it volunteered, which is the useful kind: **backward slicing was
not the win.** `elaborate_drat_to_lrat_backward` already emits fully core proofs
-- slice fraction **1.0000** on every instance measured. The slice removes only
unused *input clauses* (7,808 -> 620 hypothesis axioms on F_141). CPS plus
aliasing is where the speedup lives. It expected the opposite and said so.

### The differential, done well

Both routes end at `False`, so "same statement" is trivially true and useless.
It built the audit around **what `False` is proved from**: decoding each
hypothesis axiom back out of its `Prop` encoding. Across 9 dual-route and 11
compact-only instances -- **zero alien axioms** (every hypothesis is an actual
clause of the source CNF), **zero escapes** (compact is a subset of inlined at
every size), never empty. Three tamper controls on an emitted certificate
(weaken / relabel / permute a hypothesis) all rejected by Lean; the untampered
control accepted. Two hosts produced byte-identical modules.

### The comparison with AB Support, now measurable

**19 distinct certificates checked by official Lean v4.30.0**, up to
`R_3(x-y=5z)=286` and `R_4(2(x-y)=z)=56` (53,402 hints; 4.7 s to reconstruct,
40.7 s / 3.85 GB in Lean). `#print axioms` lists **only input-clause hypotheses
and propositional atoms** -- no `propext`, no `Classical.choice`, no
`Quot.sound`, no `em`.

That is **strictly smaller than AB Support's `[propext, Classical.choice,
Quot.sound]`**, at a scale well past their n=19. And agent-h states the caveat
itself rather than leaving it for a referee: the modules are `prelude`-mode, so
Lean is checking against **axeyum's** connectives rather than core's, and it is
a different equation family. Still four orders of magnitude short of the 741
cover.

### The P0 it found, which I verified with a control

`mod reconstruct;` lives inside `macro_rules! full_modules`, and **rustfmt does
not expand macros**. So `cargo fmt --all --check` -- part of `just check` -- is
blind to **156 modules / 221,445 lines of `axeyum-solver`, including the entire
trusted reconstruction layer.**

Reproduced here, with the control agent-a's lesson demands:

```
malformed fn appended to reconstruct/resolution.rs
  cargo fmt --all --check      -> mentions resolution.rs 0 times
  rustfmt --check <that file>  -> sees the probe 2 times
```

The workspace formatter genuinely cannot see the file; direct rustfmt can. A
formatting gate that has been green over the trusted proof layer for the life of
the crate.

Note the shape: **not a gate that ran zero tests, a gate that ran on a subset
nobody had measured.** That is a new variant of today's disease and probably the
most under-checked one -- `--all` reads as "everything".

### Attribution note

`cargo test -p axeyum-solver --lib --features full` does not compile in the
worktree right now. Checked before attributing: the only modified files are
`axeyum-cas/{groebner_cert,lib}.rs` and `axeyum-solver/{cas_certificate,cas_poly}.rs`
-- **agent-i's in-flight CAS bridge**, not agent-h's, whose work is committed
(`1b2b13c70`, `f43555625`) and which reported 1128 lib tests passing at its own
commit. I could not independently re-verify that count while another lane is
mid-edit, and I am recording that rather than asserting it.

## 06:xx — agent-a closed out. Its self-analysis is the most useful thing it wrote.

Verified from committed HEAD: `validate-claims.py` **102 claims, 0 errors**;
`check-claim-certificates.py` **102 claims re-checked, 0 errors, 23 not
re-checked**. Concept refs moved **129 pending -> 84**; all 48 Schur claims now
pin `ce3e2a52...` with `C:schur-number` resolved, verified at that exact commit
with `git cat-file -e` rather than in the working tree.

It checked my correction rather than accepting it, and confirmed all three
parts -- including that exhibiting a colouring bounds the least-`N` threshold
**from below**, which it noted is the part it would most likely have got
backwards.

### The observation worth keeping

On the bound-as-value defect, it made the point sharper than I did:

> the ledger enforces this perfectly -- `supports` reads `S > 119` or
> `S <= 120`, never `S = 120` -- and the rigour stops dead at the sentence
> boundary.

And the self-indictment is exact: the *entire structure of its task* was that
distinction. Ten cells were open precisely because
`S >= s*t*u - t*u - u - 1` is a theorem while the equality is a conjecture. It
spent the day building a gate that refuses to call a cell decided without both
a witness and a proof, then wrote a bound as a value in the next file it
touched. My `w(2;3,20) = 389` was the same error in the opposite direction,
twelve hours apart.

So the pattern is not three coincidences: **structured evidence in this project
is disciplined and prose is not**, and every number that escapes into prose
loses its relation. Its proposed fix is concrete and cheap -- a numeric claim in
prose carries its relation and citation adjacent, the way an evidence row does:
`S(6) >= 537 (exhibited colouring, Song-Mao Table 1)`, eight words that cannot
decay into a false value. Plus a linter over bare `= <integer>` in prose wanting
a citation nearby, which would have caught all three instances. Recorded as its
FEEDBACK item 14; the recurrence sites are enumerable (`SEMANTICS.md`, family
doc comments listing known values, `docs/research/` notes).

### Left open, and unowned

**84 concept refs remain pending**, now on the Rado and vdW claims rather than
the Schur ones. I measured earlier that most of that population resolves
against the current graph -- it is stale-false, not absent. Both owning lanes
have finished, so this is unassigned cleanup: re-resolve and re-pin, same pass
agent-a just did for its 48.

## 07:xx — agent-g complete. The binding constraint moved, and three campaign numbers were wrong.

### The measurement

Peak RSS from `/proc/self/status` `VmHWM`, release, on the four largest
committed certificates: **8.00x-9.98x -> 1.49x-2.13x**. A **5.4x reduction**,
and faster (F_256: 57.0-91.6 s -> 23.6-50.5 s, measured alternating).

**The headline consequence is concrete.** `rado-r4-a2-b3` -- the 226
certificate, 18.9 GB -- needed 125-151 GiB and was therefore re-checkable on
**no host in this fleet** (123 GiB maximum). It now needs ~28 GiB. The claim
"we ship certificates we cannot check" was not rhetorical, and it is now false.
At 1.5x: s5/s6/s7 go from ~2.6 GB to **~14 GB** of checkable proof, s0/s4 from
~12.3 GB to **~65 GB**.

Differential verified here: `axeyum-cnf` 372 lib tests pass, 64 DRAT tests
pass, nonzero counts confirmed. Its suite was **written before the
optimisation** -- 400 deliberately corrupted proofs, 600 arbitrary step
sequences, both routes over each real certificate in one process with verdicts
compared including the failing step index, and every randomised category
carrying a control that fails if the generator stopped producing the
interesting case. Zero disagreements.

### Three numbers this campaign was carrying that are wrong

1. **agent-c's 6.6x was the optimistic end, not the typical one.** The ratio
   *falls* with proof size; 8x is typical. So the constraint was worse than the
   number everyone including me quoted all day.
2. **agent-a's "7x `CnfFormula` overhead" is measurably 2.13x** against a flat
   arena. agent-g's warning is the useful part: *sizing the fix against 7x would
   make a correct fix look like a failure.* **I had propagated the 7x into my own
   `ACTION-ITEMS.md`; corrected in place.**
3. **agent-b's "large per-call fixed cost" is not per-call.** Measured at
   0.41 us per call; the cost is per-**formula**, 165 ms on `F_741` -- so
   **17.2 minutes of redundant work across a 6,241-cube cover.** Same symptom,
   completely different fix.

Plus a methodological one worth keeping: **any head-sampled statistic of a DRAT
proof is biased** -- a 0.1% head sample over-estimates mean clause width by up
to 2x.

### Two process findings, both the day's disease

- It **nearly reverted correct work** on an apparent 2.5x slowdown that was
  machine load (average 34 on 24 cores). Memory was reproducible to 0.1% from a
  single run; wall time needed alternating pairs. A measurement taken under
  contention is not a measurement.
- In final verification it found **`cargo clippy` exiting 0 over a *cached*
  example that had a warning** -- another gate reporting success over work it
  did not do, and the second gate-scope hole found today after `cargo fmt
  --all` being blind to 221,445 lines.
- Its ADR index line was **silently overwritten by another lane**. Campaign
  rule 9 materialising for the third time; shared append points remain
  unprotected by pathspec discipline.

## 08:xx — agent-h update: the frontier moved 86x, and my "four orders of magnitude" was wrong

### What reconstructed

`rado-r4-a1-b1/F_45` — `R_4(x-y=z) = 45` — through the compact route:

```
compact  ok true  arena 346,478,195  rss_kb 25,841,560  s 1945.993  False
audit    compact_alien_axioms 0  compact_footprint 1802  source_clauses 2472
```

150,594 resolution steps, **4,572,930 LRAT hints**, 346M kernel expression
nodes, 24.6 GB, 32.4 minutes, closing to a `False` the trusted kernel accepts —
with all 150,594 clause aliases type-checked by `add_declaration` on the way.
**86x more hints than anything reconstructed before this session.** The inlined
route on the same instance: 5.8 GB after 46 minutes, no result.

At scale the constants came out *better* than the small-instance curve
predicted — 75.8 nodes/hint and 76.4 B/node against a predicted ~80 and
90-100 — so its own 34 GB estimate was conservative by 38%. Worth noting because
extrapolations in this campaign have mostly run the other way.

It states the limit itself rather than leaving it: **not externally
Lean-checked.** Rendering is ~1.7 GB of source at a measured 160 KB/s (~3
hours), and Lean needs ~190x module size in RAM (~320 GB). The largest
*externally* Lean-checked certificate remains `r4-a2-b1/F_56` at 53,402 hints.

### My framing error, caught by the agent

I wrote that this work was "four orders of magnitude short of the 741 cover".
**That compares total steps across 6,241 cubes to a single reconstruction.**
699,572,027 / 6,241 is ~112,092 steps per cube — **smaller** than `F_45`'s
336,432 DRAT steps. A single cube of the open claim is *inside* what just ran,
not beyond it.

agent-h nearly published the wrong version too, and recorded the caveat I would
want: it does not know the two counts measure the same thing, and one real cube
should be measured before anyone plans on it. That is the right level of
confidence — the arithmetic is suggestive, not established.

### The next wall, named

**The Lean render, not the arena.** 160 KB/s throughput, and above ~100k hints
the emitted module is uncheckable by Lean anyway. Its proposal is right and I
would adopt it: a **size-aware policy** — render below a threshold, report the
kernel verdict above it. Emitting a 1.7 GB file nobody can check is worse than
declining to emit one, because it looks like evidence.

That is now the third distinct wall this campaign has found by hitting it:
proof checking (agent-g, moved 5.4x), reconstruction arena (agent-h, moved
5.6x), and now rendering. Each was invisible until the one before it moved.

## 09:xx — agent-i complete. Brief error #5, and the best self-check of the campaign.

Verified here: tree clean, `cargo test -p axeyum-solver --lib --features full`
**1128 passed / 0 failed**.

### My brief was half wrong, and the wrong half was the expensive one

I sent it to wire Sturm sequences, real algebraic numbers and interval
arithmetic from `axeyum-cas` into the solver. **Three of those four flagship
capabilities already exist in the solver, better.** Measured:

```
crates/axeyum-solver/src/nra_real_root.rs   7684 lines
crates/axeyum-cas/src/sturm.rs               303 lines
```

Wiring Sturm in would have been a **downgrade**. My "465 functions, 2
touchpoints" framing counted the *bridge* and inferred a *capability gap*; the
capabilities were largely duplicated, not absent. Fifth brief error of the
campaign and the same shape as the other four -- a real measurement, a wrong
inference from it.

It also hit the 10x counting trap I warned it about and caught it: 465 public
functions, **213 of them indented inside `impl` blocks** and invisible to
`grep '^pub fn'`.

The genuine gap was narrow and real: `ideal_contains` returned `Option<bool>`,
and **a bare bool is not evidence under ADR-0386's own standard.** `groebner.rs`
had zero certificate vocabulary.

### What the bridge bought

`cas-ideal-refuter`: cofactor-tracking Buchberger emitting
`target = sum c_i*g_i + r`, with a checker that re-derives the identity with no
CAS code in the loop. Previously `unknown`, now decided -- `mod` atoms 801 ms ->
83 ms, `div` atoms 1.24 s -> 60 ms, and **the Rado `L3` shape over three `div`
atoms: 20 s timeout -> 207 ms.**

Two counter-measurements changed the design, both worth keeping:

- its first placement was a **regression** -- `x+y=3 & x*y=5` was already
  decided faster by `nra-real-root` -- so the route moved behind the existing
  engines rather than in front;
- **the campaign's 60 s Rado-lemma timeout was the monolithic hypothesis set,
  not the shape.** In minimal form those lemmas are already solved by
  `int-real-relax`. That is direct evidence for roadmap item 4
  (lemma splitting / hypothesis minimisation) and it means the `forall`-route
  stall may be a *decomposition* problem rather than an algebra problem.

### The self-check that redeems the whole campaign

It first reported **"13 of 13 controls fire"** on the strength of stubbing the
entire checker. Then it ran the *strong* mutation -- delete one guard at a time
-- and found **six of seven guards could be removed with every tamper test still
green.** They all rejected through the identity check, so the suite was testing
one thing six times.

It replaced them with six **forgeries**: valid certificates for *satisfiable*
queries with exactly one guard standing between them and a wrong `unsat`
(`x^3 = -1` is satisfiable at `x = -1`; presenting `x^3` as non-negative gives a
clean `-1`). Each guard deletion now kills exactly one forgery and no other. One
guard is documented as *conservative rather than load-bearing*, with the reason.

This is agent-a's "four of five controls did not fire" lesson applied one level
deeper -- to the mutation strength itself -- **and caught by the agent on its
own work, after it had already published the flattering number.** It is the
best piece of self-review anyone produced.

### Honest non-result

I3 not discharged, with a precise obstacle rather than a shrug: **the
certificate is a statement about R and the Rado lemmas are true over Z for
reasons involving integrality.** Its follow-ups (exact-rational LP over
candidate residues; integrality certificates via a modulus plus finite
enumeration in Z/mZ) are the right next moves and are as re-checkable as a
polynomial identity.

Also flagged: two Sturm/algebraic implementations with different caps, no shared
tests, and `interval_arith::abs()` **panicking** where every sibling returns
`None`.

## 10:xx — agent-c complete. A second new value, and agent-g's fix retroactively unblocks its biggest loss.

Verified: **103 claims, 0 errors** on both gates.

### `R_4(5(x-y)=2z) = 625` — NEW, both sides certified

Construction witness at 624; **103,409,097-step DRAT refutation** at 625. Blank
in CDLW Table 10, inside the `a >= b+2, gcd = 1` hypotheses, untouched by Li
(their family maps onto our `b = 1` column only). That is the campaign's
**second genuinely new exact value**, after `741`.

It shipped without a `novelty` field — the same gap `741` had — so I labelled it
(minimal one-line insert, `b00616493`). Twice now the campaign's new values have
reached the ledger unlabelled, which is an argument for making the field
required rather than optional once the legacy backfill is done.

**Census dispute resolved against Li**: Table 10 row `b=1` reads
`45 56 81 256 625`, so Li's `"NEW": true` on `b=5 -> R_4 = 625` is a 2022 ISSAC
value. Our census stands.

And the audit I most wanted to see: **all cells, not a chosen subset** — 25/25
Table 1 and 10/12 exact Table 10, **zero mismatches**. That is last session's
worst error (a formula "verified against 15 published values" the author had
chosen) answered directly.

### The unblocking, which is the real news

`(5,3,4)` at n=625 was **killed mid-solve at 3h11m with 15.51 GB of proof** —
and killed *deliberately*, because at the then-current ratio its check would
need **~102 GiB, more than any host in this fleet has.**

agent-g moved that ratio from ~8x to **1.49x-2.13x** hours later. At 1.5x a
15.51 GB proof needs **~23 GiB** — comfortable on s0 or s4, and plausibly within
reach of the 26 GiB boxes.

So the memory work did not merely improve a number: **it retroactively converts
a result this campaign abandoned as impossible into a routine run**, and that
result is the last blank cell of the `a >= b+2` row we were testing. That is
the cleanest possible validation of an infrastructure improvement — a specific
named thing that could not be done before and can be now.

Also unblocked by the same arithmetic: `(6,1,4)` at n=1296 (killed at 6.03 GB),
and `rado-r4-a2-b3`'s shipped 18.9 GB certificate, which needed ~125 GiB and was
re-checkable on **no host here**.

### Unresolved, stated exactly

`(5,3,4)` n=625, `(6,1,4)` n=1296, `(4,1,5)` n=1024 (cover 658/15,625 cells),
`(2,1,5)`. **All four have their lower bound established and their refutation
not.** Nothing rounded.

## 11:xx — agent-j complete. The negative-control suite exists, and its guard caught its author.

### The census, with my misreading corrected

I reported "163 rows, 15 unlabelled". Wrong: the file is **15 `#` header lines
plus exactly 148 data rows, none unlabelled.** I counted lines and inferred
rows. Same shape as every other counting error this campaign -- measure the
construction before counting the output.

| code | meaning | n |
|---|---|---:|
| `A1` | the distractor text **is itself** a false proposition in a fragment we decide | **49** |
| `A2` | refutable after **one** standard formalisation choice | **37** |
| `B` | genuine proposition, out of fragment (column names what it needs) | 17 |
| `C-*` | not a checkable proposition at all | **44** |
| `DEP` | deprecated, excluded | 1 |

**A = 86/147 (58.5%)**, denominator 147 rather than 148 because one file is
deprecated.

Two caveats it volunteered rather than buried, and both are the right instinct:
`C` came out **smaller than I predicted** because this is a *school*-mathematics
corpus that overlaps our fragments by construction, so 58.5% measures **this
corpus, not "real mathematical error"**; and **A1 = 49 (33%) is the number that
survives a hostile reading** -- it named the five weakest A2 rows so a sceptic
can demote them and land at 55%.

### The suite

**32 built, 32 refuted, 0 unknown, 0 wrong**, plus 3 must-be-SAT controls with
evaluator-rechecked witnesses, ~90 ms through the real AIG -> CNF -> SAT path.

**Its guard fired on its own author, on the first run.** Beyond the must-be-SAT
control it added a fifth test -- *premises-minus-claim must be satisfiable* --
and its own `one_has_two_distinct_divisors` failed it: the claim was a
tautology because `d != e` had been put in the premises. **Four tests stayed
green; that one said "the premises alone are unsatisfiable, so its refutation
proves nothing."** Mutation-tested afterwards: no guard is removable with the
suite green.

That is agent-i's lesson (six of seven guards removable under a strong
mutation) applied *before* the mistake shipped rather than after.

### The structural finding, which is the roadmap item

`check_unsat` proves UNSAT **by enumeration**, and `lib.rs` `unreachable!()`s on
`Sort::Int` / `Sort::Real`. So **the ordered-field half of the stack is
structurally incapable of carrying any negative control** -- 11 QF_LRA
candidates declined for that reason, and 15 of the 86 refutable rows are
naturally QF_LRA. An UNSAT evidence route for `Int`/`Real` in
`axeyum-scenarios` is the single change that most enlarges this.

### Corpus errors, found and reported rather than corrected

1. **`fraction-is-two-numbers-not-one.md:25`** -- verified here. The distractor
   is *"3/4 has to be bigger than 1/2, because 3 and 4 are both bigger than 1
   and 2."* **The conclusion is true**; only the reasoning is wrong. It is the
   only one of its kind in the corpus, and **anything consuming
   `distractor_forms` as false statements will mark a correct answer wrong.**
   The file is not pedagogically wrong -- right answer, wrong reasoning is a
   real misconception -- so the defect is the *assumption* that a distractor is
   a false proposition. That wants a schema field or an `AUTHORING.md` note,
   which is the graph owner's call, not mine.
2. `even-means-ends-in-even-digit.md:16` -- "3.4 is even" is **ill-typed, not
   false**.
3. **Ten live near-duplicate pairs**, two sharing an identical distractor
   string.

### Curriculum

14 -> 15 of 23 nodes now carry evidence. **`divisibility-and-euclid` claimed
`computable` / `covered` with zero negative-control evidence**; closed with four
parity/divisibility controls, so `decidable` and `computable` are now fully
evidenced. `reals` is the one `covered` node the corpus cannot support at our
fragment -- an honest gap, recorded.

It also declined to add an `artifacts/examples/` pack on the grounds that a
nonconforming one would break `just check` for every lane, and the Rust suite is
the stronger artefact because the solver gate actually runs it. Correct call.

## 12:xx — agent-k complete. The B4 folklore is now measured, and the k=3 blocker was misdiagnosed.

Verified: `cargo test -p axeyum-solver --lib --features full` **1138 passed**
(1128 + 10). `const MAX_CROSS_PRODUCTS: usize = 2` confirmed at `nra.rs:107`,
enforced at `:334`.

### The boundary is not what the register said

B4 asserted "minimal hypotheses beat a bigger budget". I flagged that as
asserted-not-measured when briefing. It is now **measured, and true for a
sharper reason than the phrasing implies**:

- **Count is a slope, not a cliff.** The lemma still closes in 2 ms with
  **forty** irrelevant degree-3 hypotheses added. No boundary at n=40 across
  four padding kinds.
- **One hypothesis is the whole boundary.** `L3`'s minimal set closes in 1 ms;
  adding exactly one of `H`'s other members flips it to `unknown` for 4 of 10
  candidates.
- **The mechanism is a named constant, not a search.** `MAX_CROSS_PRODUCTS = 2`
  is a *deterministic admission cap*: the query declines in **40 ms at 1 s,
  10 s, 60 s and 300 s alike**, and stays `unknown` through the **1800 s** rung.
  So it is not "a bigger budget loses" -- **budget is irrelevant by
  construction**, which is a stronger and more actionable statement.

It also killed its own wrong inference on the way: the route trace makes
`int-real-relax` look unreached in failures, but `auto.rs:3865` only records it
on *success*. Reading the source rather than the trace settled it.

### What closes now

`minimize_hypotheses` grows subsets from below -- `auto::unsat_core` is
structurally unable to help, since `auto.rs:664` returns `None` unless the full
set is already solver-`unsat`, which is exactly the failing case. Two goals that
were `unknown` at 1800 s now close in ~2 s, and **the subsets it finds are
exactly the ones the human found after four attempts and ~32 minutes.**

The whole colour-1 case is **NOT** found: it needs a *chain*, not a subset.
Recorded as such.

### The mutation matrix, with two honest negatives

One deliberate wrong answer produced by deleting two guards together
(`Closed { indices: [] }` for a false goal). Per-guard kills: vacuity 2,
re-verification 1, probe strictness 8, shrink strictness 8, goal pin 6/6/**0**.

Two negatives it volunteered rather than hid: **re-verification was a dud on the
first round** -- deletable with all nine tests green -- until it added a control
for it; and the shrink pin **remains** a measured dud, recorded as *conservative,
not load-bearing*, with the paired deletion showing it kills nothing extra.
That is the third lane to find its own controls weaker than claimed, and the
second to publish the dud rather than quietly delete it.

### The k=3 blocker was misdiagnosed, and the real one is small

The register's recorded obstacle -- "degree-3/4 inequalities in three
variables" -- **is proved in 2 ms** with a firing control. The actual obstacle is
**integer rounding of a nonlinear bound**:

```
P>=1, P*s >= P+1  |-  s >= 2      unknown
                  |-  s >  1      0 ms
   s > 1          |-  s >= 2      0 ms
```

Each half is instant; the composition is not. And the case analysis has **one**
leaf where `b < a` can matter, not ten. The critical leaf's arithmetic core
discharges step-by-step -- 7 lemmas, <= 2 ms each, controls firing -- once `a*b`
is abstracted.

**k=3 is not proved** and it says so: the composition and twelve leaves are
unencoded. But the shape of the remaining work changed from "we need a stronger
nonlinear engine" to two named passes: normalise integer bound strictness
(`x >= k` <-> `x > k-1` over `Sort::Int`) and a product-abstraction weakening
pass. Both are small.

### Disclosure

Its `PLAN.md` commit swept the Lean lane's uncommitted `PLAN.md` edit. Nothing
lost -- their text landed -- but the attribution is wrong, and it disclosed this
in the commit message and diary rather than attempting history surgery under a
live codex session. Correct call, and **campaign rule 9 (shared append points
are not protected by pathspecs) for the fourth time today.** The session
protocol tells every lane to edit `PLAN.md`; that instruction is the defect.
