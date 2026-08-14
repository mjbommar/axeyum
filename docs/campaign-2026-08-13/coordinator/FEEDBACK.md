# Coordinator feedback for the axeyum roadmap — 2026-08-13

## F-C1 (P1) — The Lean export is rejected by real Lean, and the toolchain was here all along

**Two findings, and the second only became visible because the first was wrong.**

### The toolchain was never absent

`docs/plan/next-actions-from-the-rado-paper-2026-08-12.md` item A2 states that
`lean`, `lake` and `elan` are "all absent on the machine that produced it
(verified)". Measured today on s0:

```
$ ls ~/.elan/toolchains
leanprover--lean4---v4.30.0
$ ~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean --version
Lean (version 4.30.0, x86_64-unknown-linux-gnu, commit d024af09, Release)
```

`elan` itself is genuinely absent (`~/.elan/bin` does not exist), and `lean` is
not on `PATH` — so `which lean` fails and the audit concluded the toolchain was
missing. It was unpacked in `~/.elan/toolchains` the whole time, matching the
repository's own `lean-toolchain` pin (`leanprover/lean4:v4.30.0`) exactly.

This is another entry for the CLAUDE.md "tools have lied more often than the
solver has been weak" list: a **negative** probe result (`which` finds nothing)
was read as a fact about the machine.

### The export does not typecheck

A2 promised that "one command on any host with a toolchain converts *we emitted
a Lean module* into *an independent kernel accepted it*." The command now has an
answer:

```
$ lean proofs/shell_closed_form.lean      # in ../axeyum-rado-paper
... 22 errors ...
EXIT=1        real 0m0.175s
```

It fails in under a fifth of a second. The module is 56 lines / 42 KB, and its
`0 sorry / 0 axiom` property is real — but nothing had ever checked that Lean
*accepts* it, so the paper's Lean claim rests on inspection, not on a kernel.

### Root cause, isolated by minimal edits on a copy

Three distinct layers, found by fixing each and re-running:

1. **Codegen.** `def rado.add` and friends are recursor-based and fail with
   "code generator does not support recursor `AxNat.rec`" / "consider marking it
   as `noncomputable`". Cosmetic: the emitter should mark these
   `noncomputable def`. They are proofs, not programs.
2. **Self-reference with explicit universes.** Line 10 emits
   `Eq.{u}` *inside* the `Eq` inductive's own constructor. Lean rejects it
   ("`Eq` is a local variable"), the inductive never enters the environment, and
   every later reference cascades into "Unknown identifier `Eq`". Nineteen of
   the twenty-two errors are this one defect.
3. **Parameters vs. indices — the real one.** The emitter declares

   ```lean
   inductive Eq.{u} : ((x0 : Sort (u)) -> ((x1 : x0) -> ((x2 : x0) -> Prop)))
   ```

   which makes `α` and `a` **indices** (zero parameters), while every
   `@Eq.rec.{0,1} α a motive minor b h` application in the module assumes they
   are **parameters**. The in-tree kernel generates a recursor consistent with
   its own declaration form, so it accepts the module; Lean generates a
   different recursor and the application does not typecheck. Rewriting the
   declaration to parameter form (`inductive Eq.{u} (x0 : Sort u) (x1 : x0) :
   x0 -> Prop`) advances the failure but does not clear it — the terms are
   fully-explicit *kernel* terms being handed to Lean's *elaborator*, which
   re-infers implicits and universes and starts inserting coercions
   (`Unknown constant CoeFun`, under `prelude` there is no `CoeFun` to insert).

### The fix is a route change, not a patch

`crates/axeyum-lean-kernel/src/lean_pp.rs:1-9` states the output is "the surface
syntax a real Lean 4 kernel reads, so a refutation the in-tree Kernel accepts
can also be ... re-checked by an independent Lean toolchain." That is the claim
under test and it is false as written: **`lean file.lean` runs the elaborator,
not the kernel.** Surface syntax makes the artifact hostage to implicit-argument
inference, universe unification, coercion insertion and codegen — four systems
that have nothing to do with whether the proof term is well-typed.

The project already has the right shape on the other side: `axeyum-lean-import`
consumes **official `lean4export` NDJSON format 3.1.0** fail-closed
(`crates/axeyum-lean-import/src/lib.rs:1-11,51`). The export path should be
symmetric — emit `lean4export` format and validate with an export-format checker
(`leanchecker` ships in the pinned toolchain at
`~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/leanchecker`; Trepplein and
`lean4export` are the other consumers). That turns "a kernel accepted it" into a
claim about a kernel rather than about a parser.

Keep `lean_pp` — a readable projection is worth having — but **restate its doc
comment to what it is** (human-inspectable rendering) and stop implying external
re-checkability until the export route exists.

### Actionable items

- **L1.** Emit `lean4export` format 3.1.0 from `axeyum-lean-kernel`; validate
  round-trip against `axeyum-lean-import` (we consume the format already, so the
  round-trip is a free differential test) and against `leanchecker`.
- **L2.** Correct `lean_pp.rs:1-9`'s doc comment now; it is the load-bearing
  claim behind the paper's Lean paragraph.
- **L3.** Fix the three surface defects anyway (noncomputable, self-reference
  universes, parameter form) so the readable projection is also *valid* Lean —
  it is cheap and it makes the artifact inspectable in an editor.
- **L4.** Put `lean` on `PATH` in the repo's tooling and add a gate that runs the
  export through an external checker. A claim nothing checks will drift; this one
  already did.
- **L5.** Correct A2 in `docs/plan/next-actions-from-the-rado-paper-2026-08-12.md`
  and the paper's Lean paragraph: the toolchain is present, the export is
  rejected, and the reason is architectural.

Reproduction, start to finish, is in
`coordinator/logs/lean-export-check-2026-08-13.md`.

## F-C2 (P1) — Correction and sharpening of F-C1's proposed route

Reconnaissance after writing F-C1 changes two things in it. Recording the
correction rather than editing F-C1 silently, because the first version would
have sent an agent down a dead end.

### `leanchecker` is the wrong target

F-C1 named `leanchecker` as the external validator. It is not one for our
purpose: its strings (`Could not find any oleans for:`, `l_Lean_findOLean`)
show it re-checks compiled **`.olean`** modules, not export text. And Lean 4.30
has no built-in export flag -- `lean --help` offers `-o` (write olean) and
`--json` (diagnostics), nothing else. `lean4export` is a separate tool and is
not installed here.

### The bridge already exists in one direction, with official fixtures

This is the part F-C1 understated. `axeyum-lean-import` consumes official
`lean4export` NDJSON 3.1.0 fail-closed, and the repository ships **genuine
v4.30 fixtures matching the installed toolchain** under
`docs/plan/fixtures/lean4export-v4.30-*.ndjson`, with a real suite behind them
(`lean4export_v31.rs`, `official_construct_matrix.rs`,
`official_mutual_inductive_groups.rs`, `official_nested_inductive_groups.rs`,
`official_recursive_computation.rs`, `wire_mutation_corpus.rs`).

So the honest statement of the Lean position is not "we are not connected to
Lean". It is:

- **Lean to axeyum: works, and is tested against official v4.30 exports.** Our
  kernel independently admits Lean's own mathematics.
- **axeyum to Lean: broken**, for the architectural reason measured in F-C1.

That asymmetry is worth stating in the paper exactly that way. It is a stronger
claim than the vague one, and it is checkable.

### The validation to build first needs no external tool

Emit `lean4export` NDJSON 3.1.0 from `axeyum-lean-kernel`, read it straight back
through `axeyum-lean-import`, and compare **ADR-0350 canonical identity
manifests** -- per-declaration structural content and direct-dependency digests
that by construction ignore wire and arena allocation order.

Emitter and importer would be written against the same external specification
but share no code, so a round-trip reproducing the identity manifest is a
genuine differential test rather than a tautology. It also reuses machinery
already built and already trusted for the import direction.

Revised item list: **L1a** round-trip emitter + identity-manifest equality
(no external dependency, do this first); **L1b** external acceptance by a
third-party checker (Trepplein / nanoda / lean4lean) or via oleans produced by
Lean itself -- scope after L1a. L2 is done (`febbcc991`). L3-L5 unchanged.

## F-C3 (P0, strategic) — The differentiator is the certificate, not the architecture

Established by source audit today, not by argument.

A solo preprint author (A. C. Li, SSRN 6814341, artifacts at
`crabsatellite/rado-numbers-sat`, Zenodo DOI 10.5281/zenodo.18957993) built, by
March 2026, for the same family axeyum spent a day on: a SAT encoder, a claim
ledger (`lean4/RadoNumbers/Ledger.lean`), a Lean 4 + Mathlib formalisation, an
axiom audit, and a public reproduction script. **The "SAT + Lean + ledger"
architecture is not distinctive.**

What *is* distinctive is visible in one line of their `SAT.lean`:

```lean
axiom lem_keypair_sat (b k : ℕ) ...
```

justified by a doc comment ("all UNSAT under CaDiCaL 1.5.3") and honestly
labelled `gapOpen Cat 2 SAT-verified`. Their SAT results **enter Lean as
assertions**; every downstream theorem is conditional on an axiom whose warrant
is an uncertified solver run.

axeyum's position is the mirror image: our SAT side is certificate-backed
(own CDCL, streamed DRAT, own backward checker, model replay, ledger with
regeneration-checked instance pins) and our **export to Lean does not work**
(F-C1/F-C2, seam S1).

Two consequences for the roadmap, and I think they reorder it:

1. **L1a moves to the top.** Closing the export direction is not a
   documentation nicety; it is the only thing that converts "we have better
   evidence" into a claim someone else's proof assistant can check. Until then
   both projects have an unbridged gap, and theirs is the one with a Lean
   theorem attached.
2. **Never ship a Lean artifact whose SAT input is an axiom.** If we bridge by
   asserting our own results, we have reimplemented their gap with more steps.
   The value is in a DRAT-checked refutation that a Lean kernel accepts *as a
   proof*, or in an explicit, audited statement of exactly what is assumed --
   their `AxiomAudit.lean` is the standard to beat, and right now it is a
   standard we do not meet, because our `#print axioms` line has never run.

Related smaller finding, same audit: our novelty claims need a literature check
**before** compute, not after. Five of eleven "new" values had been published
in April 2026 in a table one PDF extraction away. Nothing was lost -- they
became external cross-validation, and they agree exactly -- but that was luck,
not method. A cheap standing rule: for any value we are about to claim,
extract the full text of the closest paper (not the abstract) and search GitHub
for the artifact repo, before the run rather than after.

## F-C4 (P0, strategic) — Three parties shipped our architecture between June and August 2026

F-C3 said the architecture is not the moat, on the evidence of one solo
preprint. A proper literature audit -- OpenAlex phrase search across journals,
Zenodo and arXiv, run 2026-08-13 -- makes that far stronger. In the **last ten
weeks**:

| date | work | party |
|---|---|---|
| 2026-06-16 | *A Kernel-Certified Computation of the Four-Colour Rado Number `R_4(x+y+z=2w)=19`* | AB Support LLC |
| 2026-06-18 | *An Automated, Kernel-Certified Pipeline for Computing Exact Rado Numbers* | AB Support LLC |
| 2026-07-04 | *[longsystems] Autonomous formal proof: `R(x+y=3z;5) >= 40`* -- Lean-4-kernel-verified, discovered **autonomously by an agent**, with an axiom audit and the model named | Longsystems Research |
| 2026-07-29 / 08-05 | *Proof Engine Infrastructure: A Claim-Graph Framework for AI-Assisted Mathematical Research* | A. C. Li |

Read the abstracts rather than the titles. AB Support's pipeline "takes a
partition-regular linear equation and a number of colours, computes the exact
Rado number, and emits a Lean 4 certificate of the mathematically load-bearing
half -- the unsatisfiability of the threshold instance -- that the Lean kernel
typechecks". Li's Proof Engine is "an architecture for converting untrusted
generation into independently checkable mathematical claims".

That second phrase is **axeyum's own identity sentence** -- "untrusted fast
search, trusted small checking" -- and the first is the pipeline we spent today
demonstrating. Three independent parties, ten weeks, no coordination.

### What this does and does not take away

It does **not** touch the values. Nobody has computed `R_4(a(x-y)=bz)` at four
colours for `b = 4`; `741` stands (see the novelty note on that claim).

It does take away the *architectural* claim almost entirely. "SAT + Lean
certificate + claim ledger + autonomous agents" is now a small crowded field,
not a differentiator.

### The one measurable distinction left, and it may be real

AB Support report an axiom footprint of **exactly
`[propext, Classical.choice, Quot.sound]`** (explicitly no `native_decide`).
Our re-emitted module reports **`'shell_closed_form' does not depend on any
axioms`** -- an *empty* footprint, which is a strictly smaller trusted base.

**Verify this before anyone says it aloud.** It is not obviously
apples-to-apples: their certificate covers the unsat half of a Rado threshold
(a SAT refutation lifted into Lean), ours currently covers the shell-bound
*arithmetic*. The honest comparison is between certificates of the same
statement, and we have not built theirs. If our unsat-half certificate also
comes out axiom-free, that is a genuine and checkable advantage in trusted
base. If it needs `Classical.choice`, we are level and should say so.

### Actions

1. **Read all four works properly** before the paper's related-work section is
   written. Two are DOI-stamped on Zenodo and freely fetchable.
2. **Build the comparison that matters**: our Lean certificate of a *refutation*
   (not of the arithmetic), and its `#print axioms` footprint against theirs.
3. **Stop citing architecture as the contribution.** What survives is the
   measured trusted base, the DRAT certificates checked by our own checker,
   the cover obligations discharged mechanically, and specific values. Those
   are checkable; "integrated framework" no longer distinguishes us.
4. Note that a **fully autonomous agent** published a Lean-kernel-verified Rado
   bound in July with a named model and an axiom audit. The novelty of "agents
   did this" expired six weeks ago.

### F-C4 CORRECTION, same day — I overstated the venue and did not check it

Asked where those papers were, since they are not on arXiv. They are not. **All
four are Zenodo self-depositions**, surfaced through OpenAlex, and I presented
them as though they were published literature. Verified against the Zenodo API:

| work | type | creator | downloads | artifacts |
|---|---|---|---:|---|
| Kernel-certified Rado pipeline | Preprint | AB Support **LLC** | 7 | `R4_certificate_bundle.zip` **3.7 MB** + paper |
| `R_4(x+y+z=2w)=19` | Preprint | AB Support **LLC** | 7 | `R4_artifacts.zip` 318 KB + paper |
| Proof Engine Infrastructure | Working paper | A. C. Li | 5 | PDF only |
| longsystems `R(x+y=3z;5) >= 40` | Preprint | Longsystems **Research** | 2 | one **2.9 KB** markdown file |

Zenodo applies **no peer review and no moderation** -- anyone can deposit and
receive a DOI. Download counts are 2-7. Two of the four "authors" are companies
rather than people or institutions, and the longsystems abstract states outright
that its result was "discovered autonomously by the longsystems agent ...
Model: deepseek-v4-pro[1m]", i.e. an agent depositing its own output.

**What survives the correction, on the artifact test** -- the same test that
settled Li's Rado claim, where a GitHub repo with real witness files made an
unreadable SSRN preprint into genuine prior art:

- **AB Support LLC is real work and real prior art.** A 3.7 MB certificate
  bundle is not a generated abstract, and the claim is technically specific in a
  way that reads as knowledgeable -- an axiom footprint of exactly
  `[propext, Classical.choice, Quot.sound]`, explicitly no `native_decide`.
  Treat it as a serious parallel effort and read it.
- **Li's Proof Engine** is an architecture paper with no artifact. Its
  *architecture* overlaps ours; nothing is demonstrated in the deposit itself.
- **longsystems is 2.9 KB.** As prior art, negligible. As a signal that agents
  are auto-depositing Lean-verified Rado claims to DOI-issuing repositories,
  it is worth exactly one sentence and no more.

**So the corrected strategic reading:** one credible parallel effort with
artifacts (AB Support), one architecture note, one agent artifact. That is not
"a small crowded field". F-C3's core point stands -- the architecture is not by
itself the moat -- but the evidence for it is one serious party, not three.

**And I did precisely what I have been criticising all day.** I took a search
result, did not check the epistemic status of its venue, and promoted it to a
strategic claim in the same reply. The tell was visible in my own output --
the venue column said "Zenodo (CERN European Organization for Nucle" on nearly
every row and I read past it. Fifth instance today of evidence being real and
the inference running ahead of it, and the first where I had the disconfirming
datum on screen.

## F-C5 (P1) — `graph_pin` is valid; `resolved` is a stored boolean that goes stale

**First, my error, because it is the sixth instance of one pattern today.**
I reported that 39 claims pin a commit `a29a9e2a...` that "exists in no
repository on this machine" and called it a dangling pointer and an integrity
defect. The statement was literally true and the diagnosis was wrong: the local
`math-education` clone was **5 commits behind origin**. After `git fetch` the
commit is present, is an **ancestor of HEAD**, and pins exactly **1,565
concepts** -- the precise figure the findings register cites. The provenance was
working as designed.

`git cat-file` returning nothing means *not in this clone*, not *does not
exist* -- exactly as `which lean` returning nothing meant *not on PATH*, not
*not installed*. I named that pattern this morning and reproduced it this
evening.

**The real finding, measured after updating the clone.** Of 432 concept
references across 102 claims, 129 are recorded `resolved: false`:

| ref | count | status against current graph |
|---|---:|---|
| `C:rado-number` | 39 | **now present** |
| `C:ramsey-number` | 14 | **now present** |
| `TQ:colouring` | 14 | **now present** |
| `C:computational-search` | 13 | **now present** |
| `C:open-problem` | 1 | **now present** |
| `C:schur-number` | 48 | **genuinely absent** |

So **81 of 129 are stale-false** -- the concepts exist, nobody re-ran
resolution -- and **48 are a real gap**: agent-a authored 48 off-diagonal Schur
claims against a `schur-number` concept that was never written.

**The systemic point.** `resolved` is a **stored boolean**, not a re-derived
one. The ledger regenerates CNF instances to check `instance-pin` and
re-derives DRAT proofs, then takes a cross-repo reference's resolution on
trust from whenever it was last written. That is the same shape as every other
defect today: a field that looks like a check and is a memory of one.

### Actions

1. **`check-claim-certificates.py` should re-resolve concept refs against the
   pinned commit** (`git cat-file -e <pin>:graph/<kind>/<slug>.md`), not read
   the stored flag. Re-derivation is the ledger's whole discipline; this field
   is the exception.
2. **Fail loudly when the pin is not present locally**, with "fetch and retry"
   rather than treating absence as a negative result. That is the check that
   would have stopped me publishing a wrong diagnosis.
3. **Author `graph/concepts/schur-number.md`** -- 48 claims reference it. It is
   the single highest-count gap in the graph.
4. Re-run resolution and flip the 81 stale-false entries.
