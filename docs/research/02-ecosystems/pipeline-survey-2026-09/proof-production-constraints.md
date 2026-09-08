# Proof-production constraints on preprocessing/inprocessing

Lane: research-proof-constraints. Read-only research; no code, no builds, no
commits. Tag key: **[C]** = confirmed by reading code in this tree or in
`references/`, with file:line; **[P]** = paper/spec claim, cited; **[I]** =
inference from [C]/[P] facts, not independently verified; **DID NOT VERIFY** =
looked for and could not confirm, flagged so nobody downstream treats silence
as an answer.

## Bottom line

**We already built the hard part, and it already matches the literature's
answer.** `axeyum-cnf::inprocess` (ADR-1750) runs subsumption, vivification and
BVE before search, emits every derived clause into the *same* DRAT stream the
search writes to, restricts itself to plain RUP (no RAT, no extension
variables) for all three passes, and BVE's model-reconstruction stack
(`axeyum-cnf::bve::Reconstruction`) is a Rust re-implementation of the exact
CaDiCaL/Kissat extension-stack algorithm confirmed by reading their source in
this session. The open technique-by-technique question below is almost
entirely about *techniques we have not built yet* (BCE, ELS/congruence, SAT
sweeping, ternary resolution, XOR/Gaussian at the *inprocessing* level,
symmetry breaking) rather than about repairing what exists.

The one technique class this repo should treat as **out of scope for DRAT and
in scope for a different mechanism**: anything whose soundness argument is not
"this clause follows from what's active" but "removing this changes nothing
about satisfiability, by a theorem about the technique, not by resolution."
BCE is the textbook case — see §1.5 and §2.

## 1. Technique-by-technique constraint table

| Technique | DRAT-expressible? | Needs RAT? | Needs deletion info for *correctness*? | Extended resolution / new vars? | Model-reconstruction impact | Recommended for us |
|---|---|---|---|---|---|---|
| **Subsumption** (forward + self-subsuming resolution) | Yes, RUP | No | No (deletion-only steps need no justification at all, see §1.6) | No | None — model-preserving [C] `crates/axeyum-cnf/src/simplify.rs:1-45` | **Have it.** `axeyum-cnf::simplify`, wired into `inprocess_into`. |
| **Clause strengthening** (self-subsuming resolution as strengthening) | Yes, RUP | No | No | No | None — model-preserving | **Have it.** Same module. |
| **Vivification** (Piette/Hamadi/Saïs ALA) | Yes, RUP | No | No | No | None — strengthened clause is a strict literal subset, model-preserving, no reconstruction trail [C] `crates/axeyum-cnf/src/vivify.rs:1-55` | **Have it.** `axeyum-cnf::vivify`. |
| **Bounded variable elimination (BVE)** | Yes — resolvents are RUP additions; the *removed* clauses need only a plain (unjustified) deletion | No | No for the DRAT proof itself; **yes for the SAT witness** (see reconstruction stack, §2) | No — BVE eliminates a variable, it does not introduce one | **Equisatisfiable, not model-preserving.** Every `sat` model of the reduced formula must be extended before it can be checked against the original term. [C] `crates/axeyum-cnf/src/bve.rs:12-15,133-163` | **Have it, with reconstruction wired.** `axeyum-cnf::bve` + `Reconstruction::extend`. This is the one pass that is *not* free — proof size scales with the formula, see §3. |
| **Blocked clause elimination (BCE)** | **Not via ordinary DRAT addition/deletion at all — it is a pure deletion, requiring no RAT and no RUP, because a blocked clause's removal is a satisfiability-preserving theorem, not a resolution fact.** A blocked clause *is* RAT on its blocking literal (every resolvent on that literal is a tautology, trivially satisfying the RAT resolvent-check), so if you ever need to *re-add* it (e.g. reverse-direction checking) that add is RAT, never RUP. | Only if re-added; deletion itself needs nothing | **No for the DRAT proof** (drat-trim: "clause deletion steps are not checked, because they trivially preserve satisfiability" [P] `references/drat-trim/README.md:24-25`) | No | **Breaks the model exactly like BVE and needs the same extension-stack machinery** — CaDiCaL's `push_clause_on_extension_stack(c, pivot)` is called for *both* BVE and BCE clauses [C] `references/cadical/src/extend.cpp:63-71`; Kissat's `kissat_weaken_clause`/`kissat_weaken_unit` is the identical mechanism, called from block/eliminate alike [C] `references/kissat/src/weaken.c:35-55`. | **Do not have it. Safe to add, but only alongside a reconstruction stack** — see §5's "what would make it safe." Cheapest of the missing techniques to add to the DRAT stream (pure deletions cost the checker nothing) but *not* cheap to add correctly, because skipping the reconstruction wiring silently breaks every `sat` check on a formula that had a blocked clause removed. |
| **Failed-literal probing** | Yes, RUP. A failed literal `l` (assuming `l` propagates to conflict) yields the unit `¬l`, which is RUP by construction — the propagation trace *is* the RUP witness. | No | No | No | None — a learned unit is model-preserving in the usual sense (it just fixes a value every model already had, or the formula was unsat) | Not yet built as a standalone pass here; **cheapest technique to add** once wanted — same shape as vivification's conflict-before-every-literal case. |
| **Equivalent-literal substitution (ELS)** | The *learning* of the equivalence (from a binary-clause / probing chain) is RUP. The *substitution* — replacing every occurrence of the eliminated representative by the other literal — is a sequence of RUP resolvent-additions plus deletions of the old clauses, **provided the representative's defining binary clauses stay in the active set** while the substituted copies are derived. | No, in the ordinary case | Not for soundness of the additions; substitution deletes the old occurrences afterward | **No new variable**, but it *does* eliminate one (the substituted literal), so | **Same shape as BVE**: if the eliminated variable's original clauses are deleted, a model of the reduced formula must be extended by assigning that variable consistently with the equivalence, i.e. it needs a reconstruction-stack entry, not by resolution. Kissat's `substitute.c` calls `kissat_learned_unit`/propagation and `ADD_EMPTY_TO_PROOF` on inconsistency [C] `references/kissat/src/substitute.c:14-35`; DID NOT VERIFY whether Kissat's ELS pushes onto its `extend` stack the same way `eliminate.c` does — grepped `substitute.c` and did not find a `kissat_weaken_*` call in the excerpt read. | **Do not have it.** Treat as BVE-shaped for the reconstruction question until verified against Kissat's actual call graph. |
| **Ternary resolution** (resolving two ternary/short clauses to strengthen or subsume a third) | Yes, RUP — it is literally resolution, and every resolvent DRAT accepts as an ordinary RUP add if it is checked at the point of derivation | No | No | No | None if used to strengthen/subsume (same argument as subsumption); none if it only *adds* clauses (redundant, RUP-derivable) | Not yet built. Cheap technique, same emission pattern as subsumption. |
| **SAT sweeping / bounded equivalence checking** (Kissat `sweep.c`, uses a SAT sub-solver `kitten` to find structurally-implied equivalences/units) | Yes for what it *proves*: each equivalence/unit it certifies is proved by a bounded SAT call whose refutation is itself DRAT-checkable in principle, and the resulting substitution is ELS-shaped once found | Possibly, depending on how the sub-solver's result is translated back — **DID NOT VERIFY**: `sweep.c` uses an embedded solver (`kitten`) and I did not trace whether its internal refutations are re-expressed as RUP steps against the *outer* formula or asserted directly. | Not verified | Not verified — DID NOT VERIFY whether Kissat's `sweep.c` ever needs a genuinely new (extension) variable | Same as ELS/BVE once a variable is actually eliminated by the discovered equivalence | **Do not have it; highest research cost of the missing techniques** — its soundness argument is one level removed from the CNF (SAT-solving inside SAT-solving), so before adopting it we need to trace exactly how Kissat turns a `kitten` result into a DRAT-acceptable step, not assume it. |
| **XOR / Gaussian-elimination reasoning** | **Not directly** — a hand-rolled "sum of rows" resolution chain is *not* RUP-checkable in general once shared variables cancel (documented, with a concrete counterexample, in our own code: two width-2 rows summing straight to the empty clause give a non-RUP step) [C] `crates/axeyum-cnf/src/xor_drat.rs:47-52`. **The safe route is re-derivation**: extract the provenance subset `S` of original XOR constraints that Gaussian elimination actually summed to reach `0=1`, re-encode `CNF(S)` and hand it to the in-tree proof-producing CDCL core, whose 1-UIP learning materializes the RUP-checkable intermediate resolvents [C] `crates/axeyum-cnf/src/xor_drat.rs:38-53`. This mirrors CryptoMiniSat's own approach, which instead extends its proof format (FRAT) with *native* XOR clause types rather than re-deriving in plain CNF [C] `crates/axeyum-cnf/src/xor_drat.rs:32-37`, doc citing `gaussian.cpp`. | No, once re-derived through the CDCL core | No | No new variable, but the re-derivation route is strictly more expensive than the algebra it certifies | None — it is a Boolean-only `unsat` refutation of a sub-formula, no model to reconstruct on the refutation side; DID NOT VERIFY the `sat`-direction story (an XOR system found satisfiable, contributing forced units/equalities back into CDCL) | **We already solved this one — see §2 of the "what we have" section below.** `axeyum-cnf::xor_drat` is a working worked example of the general principle: when a technique's native soundness argument is not RUP-expressible, re-derive the same conclusion through the RUP-producing core over a small sub-formula, rather than inventing a proof-format extension. |
| **Symmetry breaking** | **Two very different cases, do not conflate them.** (a) Symmetry breaking baked into the *generator* — a clause set that already only allows canonical (lexicographically-ordered) colourings, so the symmetry-breaking clauses are part of the formula being refuted, not a post-hoc injection — is trivially DRAT-compatible because there is nothing extra to prove; this is what our own encoder does today (see below). (b) Symmetry breaking *injected into an already-fixed CNF* by an external tool (BreakID/saucy-style, adding symmetry-breaking predicates over the *existing* variables) is generally **not RAT-expressible and needs the strictly more powerful PR (propagation-redundant) proof system** [P] Heule, Kiesl, Biere, "Short Proofs Without New Variables," CADE 2017, LNCS 10395:130-147 — "PR gives a framework for strong symmetry-breaking inferences" precisely because ordinary RAT clauses are not always sufficient to justify an SBP addition without a fresh variable. | RAT is *not* sufficient in the general injected case; PR is the documented answer, DRAT/RAT is not | Deletion of the pre-symmetry-broken clauses (if any) is free as usual | **Case (b) generally needs PR, which subsumes but is strictly stronger than RAT** — this is a proof-system upgrade, not just an emission discipline | None directly (symmetry breaking adds clauses, doesn't remove variables) — but a *wrong* symmetry-breaking predicate can silently prune real models, which is why the soundness argument has to be checked at all | **Case (a) — have it, for free, in `axeyum-cnf::colouring`** (see below). **Case (b) — do not build it** without first deciding whether we adopt PR checking; a naive RAT-only injected SBP is an unsound-until-proven-otherwise addition to a `sat`-bearing route. cvc5 disables symmetry breaking under proof production for exactly this reason [C, restated from ADR-1704's own reading of the eDRAT paper] `docs/research/09-decisions/adr-1704-*.md`, "candidate bridges" section. |

### 1.5 The one-sentence rule this table reduces to

A pass is free to run silently in our proof format **iff every clause it adds
is RUP against the currently active set at the moment of derivation** (never
needing RAT, never needing a fresh variable). Everything in the table that
needs anything stronger — RAT, PR, or a re-derivation detour — is a technique
whose *soundness argument is not itself a resolution fact*, and that mismatch
is exactly what a checker "not growing by a line" (ADR-1704's own framing)
forbids us from teaching `check_drat`/`check_lrat` to understand natively.

### 1.6 Deletion is a performance knob, not a soundness knob — confirmed independently

Two independent sources agree, and this repo measured it a third way:

- **[P]** DRAT-trim's own README: "Clause deletion steps are not checked,
  because they trivially preserve satisfiability. The main reason to include
  clause deletion [...]" (performance, backward checking) —
  `references/drat-trim/README.md:24-29`.
- **[C]** Our own ADR-1750 measurement: dropping every `Delete` step from 38
  inprocessed proofs left **all 38 still valid**, while dropping every `Add`
  step made **all 38** rejected — the asymmetry is exactly what the monotone
  RUP argument predicts (a superset active clause set can only make later
  RUP/RAT checks easier, never harder).
- **[P]** The same README states DRAT "is therefore a generalization of
  Extended Resolution" — the theoretical ceiling of what RAT-with-fresh-
  variables can express — `references/drat-trim/README.md:18`.

## 2. Model reconstruction — confirmed against two independent implementations, and we already match them

Every technique that *removes a variable* (BVE, ELS, and any future SAT-
sweeping-driven substitution) breaks the correspondence between a model of
the reduced formula and a model of the original. Both reference solvers solve
this with the same mechanism, an **extension/witness stack replayed backward
at the end of search**:

- **CaDiCaL** (`references/cadical/src/extend.cpp`): `push_clause_on_extension_stack(c, pivot)` pushes, per removed clause, a zero-separator, the pivot/witness literal, and the clause's other literals (`extend.cpp:56-71`). `External::extend()` walks the stack **backward**, and for each entry: if the clause is already satisfied under the current partial (in-progress) assignment, do nothing; otherwise flip the *witness* literal true (`extend.cpp:118-190`). The doc comment names this exactly: *"a satisfying assignment for the original formula after removing eliminated clauses... pioneered by Niklas Soerensson in MiniSat... published at IJCAR'12"* (`extend.cpp:47-54`).
- **Kissat** (`references/kissat/src/extend.c`, `weaken.c`): `kissat_weaken_clause`/`kissat_weaken_unit` push a witness literal then the clause's other literals onto `solver->extend` (`weaken.c:35-55`); `kissat_extend` walks it backward with the identical "satisfied? skip. else pick the unassigned/witness literal" logic (`extend.c:44-120`). This function is called from **both** `eliminate.c` (BVE) and `block.cpp`/blocking code — i.e. Kissat treats BVE and BCE reconstruction as the *same* mechanism, which independently confirms the table's claim above that BCE needs identical reconstruction machinery to BVE.
- **Us**: `axeyum-cnf::bve::Reconstruction::extend` implements the *same rule*, explicitly citing it as such: "the rule (per variable, in reverse elimination order): set `x = true` ... if any clause that contained `¬x` is then unsatisfied, set `x = false` instead" [C] `crates/axeyum-cnf/src/bve.rs:146-163`, and the module doc calls it out by name: *"the `CaDiCaL` extension-stack rule"* [C] `crates/axeyum-cnf/src/bve.rs:14`.

**What this means for us:** the reconstruction mechanism is not something to
design — it is already built, tested (`crates/axeyum-cnf/src/inprocess.rs`'s
`reduction_preserves_satisfiability_and_lifts_models` test lifts a model
through `Reconstruction::extend` and asserts it satisfies the *original*
formula, `crates/axeyum-cnf/src/inprocess.rs:~370-390`), and generalizes
directly to BCE and ELS the day either lands: both need a `Reconstruction`
entry pushed at derivation time, not a new algorithm.

**What is still open:** `InprocessOutcome::reconstruction` exists but ADR-1750
itself flags that the *solver-level* caller (`sat_bv_backend`) does not thread
it end to end — "`sat_bv_backend` still checks its `unsat` against the reduced
formula... with `cnf_inprocessing` on the BVE link is trusted rather than
checked... the obstacle is that the backend also `compact()`s, which
renumbers variables and breaks the correspondence between prefix and searched
formula" [C, quoting ADR-1750's own Consequences section]. So the mandatory
requirement in this task's brief ("every `sat` must be checkable by
evaluating the ORIGINAL term against the lifted model") is **satisfied by the
crate-level API today, and not yet wired through the solver's `compact()`
step** — that is a concrete, named, open gap, not a design question.

## 3. Proof size and checking cost

Measured, in this tree (ADR-1750, `docs/research/09-decisions/adr-1750-*.md`):

| Metric | Finding |
|---|---|
| BVE proof size vs. subsumption | On a 3.1M-variable instance, BVE's DRAT prefix is **37.7M steps** vs. subsumption's **92k** — three orders of magnitude, "for the same reason" the pass adds resolvents while subsumption only deletes. |
| Checking speed, forward vs backward | `check_drat_backward` is **231x faster** than forward `check_drat` on a refutable near-threshold random 3-SAT instance (0.87s vs 200.85s over 203,528 steps) — "well past the 26x the boolean-core lane measured on its small fixture." |
| Streaming necessity | An in-RAM `VecProofSink` "is not viable" once BVE's prefix reaches tens of millions of steps; ADR-0381's streaming sink is the only route at that scale. |
| Search-time cost vs. break-even | BVE's *pass* costs 1.2–88s against a break-even of 59k–131k conflicts (median ~92k) across a 100x range of instance size — i.e. BVE only pays for itself on searches that run long enough, independent of formula size. This is why `InprocessOptions` defaults to `OFF`. |
| A second checker caught a real bug on this exact path | `check_drat` and `check_drat_backward` **disagreed** on one inprocessed proof (forward `Ok(true)`, backward `Err`) because a deletion step names a literal *multiset*, and `(b)` / `(b ∨ b)` are set-equal but multiset-different — only one of them can propagate as a unit. This is now a fixed, tested invariant across `drat.rs`, `drat_backward.rs`, and `lrat.rs` [C] ADR-1750, "A checker bug the inprocessed proof found." |

**External measurement (worked in parallel, not derived from our tree)**: the
eDRAT paper (already read into this tree's ADR-1704 as prior art) reports
proof-generation overhead **under 10%** over proofless cvc5 for its
CNF-and-theory-lemma proof stream, against **2x–17x** for cvc5's own ALF/LFSC;
checking is **3x/15x** faster than LFSC/ALF on QF_LRA and **80x/120x** on
QF_UF [P, cited in-tree] Hitarth, Codel, Lachnitt, Dutertre, "Extending DRAT
to SMT," FMCAD 2024, DOI `10.34727/2024/isbn.978-3-85448-065-5_8`. That paper
also states its own limitation, which is our limitation too, one layer
earlier: **"the preprocessing, simplification, and rewriting steps that SMT
solvers perform to convert formulas to CNF are not expressible in eDRAT"** —
and their measured mitigation (carrying preprocessing into ALF/LFSC) shows the
size cost is *"significant mostly on easy problems"* — on hard problems
resolution and theory lemmas dominate, not preprocessing. Interpreted for our
CNF-level inprocessing question specifically: **preprocessing proof cost is
disproportionately a small-problem tax; the technique that actually
determines the checking budget at scale is BVE's resolvent count, which our
own measurement above already quantifies directly.**

`references/drat-trim` and `references/cadical` carry no further quantified
overhead numbers beyond what is in their code comments; DID NOT VERIFY
whether either repo's own paper/README states an inprocessing-specific
proof-size multiplier — the closest is the Fazekas/Biere/Scholl "Incremental
Inprocessing in SAT Solving" (SAT 2019) line of work, whose abstract concerns
*incremental* solving (inprocessing across successive incremental calls, via
"clause restoration" reasoning) rather than proof size for a single query;
DID NOT VERIFY its measured overhead numbers (paper not fetched in full,
only bibliographic metadata confirmed via search).

## 4. The theory side — cvc5/Alethe/carcara

Confirmed by reading the actual rule enum and checker source, not the paper
abstract:

- **cvc5 has an explicit, named "give up" rule.** `ProofRule::TRUST`: *"This
  rule is used when a formal justification of an inference step cannot be
  provided"* [C] `references/cvc5/include/cvc5/cvc5_proof_rule.h:427-438`.
  And `TRUST_THEORY_REWRITE`: *"the checker for this rule does not replay the
  rewrite to ensure correctness, since theory rewriter methods are not
  static"* [C] `references/cvc5/include/cvc5/cvc5_proof_rule.h:441-460` — an
  explicit admission that some rewrites are trusted-not-checked *by
  construction*, not merely by omission.
- **CNF conversion gets its own fine-grained rule family**, one rule per
  Tseitin clause shape per connective — `CNF_AND_POS`, `CNF_AND_NEG`,
  `CNF_OR_POS/NEG`, `CNF_IMPLIES_*`, `CNF_EQUIV_*` (4 rules), `CNF_XOR_*` (4
  rules), `CNF_ITE_*` (6 rules) [C]
  `references/cvc5/include/cvc5/cvc5_proof_rule.h:894-1125`. This is the
  granularity answer for question 4: **CNF-ification is proof-checked at the
  clause-template level, not trusted**; it is *theory rewriting and
  preprocessing simplification* (not CNF conversion) that falls to `TRUST`.
- **Carcara (the independent Alethe checker) has the identical escape hatch
  under a different name.** Its rule dispatcher: `"hole" => |_| Ok(())` — a
  rule that unconditionally checks as valid [C]
  `references/carcara/carcara/src/checker/shared.rs:403-405`. A proof
  containing any `hole` (or `lia_generic`, an external-solver-discharged
  step) step sets `is_holey = true` and the checker still returns success,
  just flagged [C] `references/carcara/carcara/src/checker/shared.rs:106-134`,
  `references/carcara/carcara/src/checker/mod.rs:72-125,224`. Carcara also
  ships an *elaborator* that can try to discharge a hole by calling an
  external solver and re-verifying its output proof (`hole.rs:1-33`), which
  is the same shape as this repo's `NoCheckReason::UndischargedTheoryLemmas`
  in ADR-1704 — a partial check that is reported, not silently accepted as
  full.
- **Alethe spec document** (Barbosa et al., "The Alethe Proof Format: An
  Evolving Specification and Reference") exists at
  `verit.gitlabpages.uliege.be/alethe/specification.pdf`; DID NOT VERIFY its
  prose statement on preprocessing granularity — the PDF did not extract
  cleanly through the fetch tool available in this session, so I am relying
  on the code-level confirmation above (cvc5's rule enum + carcara's checker)
  rather than the spec text itself. Treat the spec's exact wording as
  **DID NOT VERIFY**; the `hole`/`TRUST` mechanism is confirmed independently
  in both implementations, which is stronger evidence for our purposes than
  the spec prose would be anyway.

**Direct comparison to our own `axeyum-cnf::alethe`**: our checker supports
`resolution`/`th_resolution`/`contraction`/`reordering`/`weakening` and
`eq_reflexive`/`eq_symmetric`/`eq_transitive`/`eq_congruent` [C]
`crates/axeyum-cnf/src/alethe.rs:760-766,852,996,1054-1057` — **and has no
`hole`/`TRUST`-equivalent rule at all.** This is a real, load-bearing
difference from both reference implementations: cvc5 and carcara both have a
first-class "give up, but say so" mechanism; we currently do not, on the
Alethe route. ADR-1704's own `NoCheckReason::UndischargedTheoryLemmas` is the
equivalent mechanism, but it lives on the two-stream CDCL(T) contract, not on
`axeyum-cnf::alethe`. Worth naming to implementation lanes explicitly: if
`axeyum-cnf::alethe` is ever asked to check a proof containing a step it
cannot discharge, today that is a hard rejection, not a graded
"checked-modulo-N" outcome — which may be exactly the discipline we want
(ADR-1704 chose "no dialect, no escape hatch" deliberately), but it is a
choice, and it is *stricter* than both reference implementations, not
matched to them.

## 5. What frontier solvers give up under proof logging

- **Symmetry breaking, in cvc5, when producing LFSC/ALF proofs** — already
  established as ADR-1704 prior art, restated here as the one item this
  survey should carry forward rather than re-derive: eDRAT's own paper
  states some useful preprocessing "must then be disabled (in cvc5, symmetry
  breaking is incompatible with LFSC/ALF proof production)" [P, cited
  in-tree, ADR-1704's "Their limitation is our open hole" section]. This
  agrees with, and is explained by, the PR-vs-RAT gap in table row
  "Symmetry breaking" above — RAT alone is not always sufficient for an
  injected symmetry-breaking predicate, and neither ALF nor LFSC (nor our
  DRAT/Alethe) implement PR checking.
- **eDRAT itself restricts to RUP-only, rejecting RAT**, specifically
  *because* combining RAT with their core-pruning optimization (discharging
  only lemmas in the unsat core) can eliminate Boolean models and turn a
  `T`-satisfiable formula `T`-unsatisfiable after a RAT addition [P, cited
  in-tree, ADR-1704 §5 "RAT — the one place the comparison changes
  something," citing eDRAT §III-B Example III.2]. ADR-1704 already worked out
  that **this hazard does not apply to our contract as decided** (our
  extended formula is fixed before checking, no core-pruning), but flags
  explicitly: *"if this route ever adopts eDRAT's core-pruning optimization
  ... then the RUP-only restriction becomes load-bearing and `check_drat`'s
  RAT arm must be disabled on that route."* This is a standing, named
  constraint on any future core-pruning optimization, not just a historical
  note.
- **CryptoMiniSat's native Gaussian elimination is not natively DRAT** — its
  proof format (FRAT) carries *native XOR clause types* rather than
  expressing Gaussian elimination as ordinary resolution [C, our own
  documentation of their approach] `crates/axeyum-cnf/src/xor_drat.rs:32-37`.
  We deliberately did **not** follow that route (format extension); we
  re-derive through the CDCL core instead, at the cost of an extra bounded
  SAT call per XOR conflict rather than a native proof-format extension. DID
  NOT VERIFY CryptoMiniSat's measured performance delta between FRAT-XOR
  output and disabling Gaussian elimination entirely — not found in the
  material reviewed this session.
- **Kissat has no native symmetry breaking, no native Gaussian elimination**
  — confirmed by absence: `grep -rli "gauss\|xor"` across
  `references/kissat/src` returned only files where "xor"/"gauss" appear as
  substrings of unrelated identifiers (`logging.h`, `internal.c`, etc.), no
  dedicated XOR/Gaussian source file [C, negative result from direct search].
  Kissat's advanced structural techniques (`congruence.c` — AND/XOR/ITE gate
  extraction and structural hashing, i.e. its version of "SAT sweeping" /
  equivalence detection) use `ADD_STACK_TO_PROOF`/`DELETE_STACK_FROM_PROOF`
  around a `pivot` literal [C] `references/kissat/src/congruence.c:1631-1670`
  — consistent with RAT-on-a-pivot reasoning, but I did **not** trace far
  enough to confirm whether `congruence.c` ever calls the `weaken_*`
  reconstruction API the way `eliminate.c`/`block.cpp` do; DID NOT VERIFY
  whether Kissat's congruence/gate-extraction pass needs reconstruction-stack
  entries the way BVE/BCE do, or is model-preserving like vivification.
  Flag this explicitly to any lane considering a SAT-sweeping-equivalent
  pass: **trace the actual call graph before assuming it's reconstruction-free
  by analogy to ELS.**

## What we already have (read directly from the tree)

1. **`axeyum-cnf::inprocess`** (`crates/axeyum-cnf/src/inprocess.rs`) —
   `inprocess_into(formula, options, deadline, sink)` runs the enabled passes
   (subsume/vivify/bve) and **streams every DRAT step to the caller's
   `DratSink` as it derives them**, so the concatenation of the inprocessing
   prefix and the search's own steps is one proof of the *original* formula
   [C] module doc, `inprocess.rs:1-60`. This directly answers "does
   `inprocess_into` already emit proof steps" — **yes, unconditionally when
   any pass is enabled**, and it is a hard invariant tested in
   `every_pass_prefix_checks_against_the_original`
   (`crates/axeyum-cnf/src/inprocess.rs`, test module).
2. **A reconstruction stack exists and is tested**:
   `axeyum-cnf::bve::Reconstruction`, threaded through
   `InprocessOutcome::reconstruction`, exercised end-to-end in
   `reduction_preserves_satisfiability_and_lifts_models` (lifts a model
   through `Reconstruction::extend` and asserts it satisfies the *original*
   formula, not the reduced one) [C] `crates/axeyum-cnf/src/inprocess.rs`,
   test module.
3. **RUP-only discipline is a stated, tested invariant, not an accident**:
   ADR-1750 decision 2, "Every step every pass emits is plain `RUP`,"
   verified by the same test above plus the module docs on `bve.rs` and
   `vivify.rs`, each stating explicitly that their emitted steps need no RAT
   support and no pivot-literal convention.
4. **The `Add`-not-`Delete` obligation is measured, not assumed**: ADR-1750's
   38/38-vs-0/38 corruption sweep is the concrete evidence behind §1.6 above,
   run against our own inprocessing path specifically (not a general claim
   borrowed from the literature).
5. **XOR/Gaussian reasoning already has a working DRAT re-derivation route**:
   `axeyum-cnf::xor_drat`, built specifically because the naive resolution-
   chain approach is *not* RUP-checkable in general — this is the worked
   example for "what do we do when a technique's certificate isn't directly
   DRAT-expressible," and the general pattern (re-derive through the
   proof-producing CDCL core over a small extracted sub-formula, checked
   independently) generalizes to any future technique in the same shape.
6. **Symmetry breaking baked into the CNF generator, not injected post-hoc**:
   `axeyum-cnf::colouring::ColouringProblem::encode` includes symmetry-
   breaking clauses (colour-class ordering) as part of the *encoded* formula
   [C] `crates/axeyum-cnf/src/colouring.rs:28-31`. Because these clauses are
   part of the formula being refuted, not added by an inprocessing pass to
   an already-committed formula, they carry none of the RAT/PR hazard in
   table row "Symmetry breaking" case (b) — this is the pattern to prefer
   wherever symmetry is known at generation time.
7. **ADR-1704 (CDCL(T) two-stream contract)** is the sibling document for
   *theory* lemmas rather than *CNF-level* inprocessing, but it is directly
   relevant to any lane combining inprocessing with theory reasoning: the
   `theory_lemmas`/`theory_lemmas_unchecked` counted-metric pattern is this
   repo's general answer to "what do we do about a step we can't fully
   discharge," and it is the pattern §4 above shows cvc5/carcara converged on
   independently (`TRUST`/`hole`), which is corroborating rather than novel
   evidence that the pattern is right.
8. **The one confirmed open wiring gap**: `sat_bv_backend`'s solver-level
   inprocessing entry point checks `unsat` against the *reduced* formula and
   loses the `reconstruction` link across its own `compact()` step [C,
   quoting ADR-1750's Consequences section verbatim, see §2 above]. This is
   the concrete, already-diagnosed next task for any lane that wants
   solver-level (not crate-level) inprocessing to satisfy this repo's
   "every `sat` must be checkable against the original term" rule.

## 5. What would make an unsafe technique safe (per row, condensed)

- **BCE**: add a `Reconstruction`-stack push at the same emission site as the
  deletion (mirroring `bve.rs`'s pattern exactly — same struct, same
  `extend()` replay rule); the DRAT side needs nothing beyond a plain
  `Delete`.
- **ELS**: same as BCE/BVE — a `Reconstruction` entry per eliminated
  variable, RUP additions for the substituted clauses, ordinary deletions
  for the originals; do not assume it's reconstruction-free without tracing
  Kissat's `substitute.c` call graph further (not confirmed either way this
  session).
- **SAT sweeping / structural equivalence (`congruence.c`-shaped)**: trace
  the actual proof emission before adopting — DID NOT VERIFY whether it's
  RUP-only, whether it needs reconstruction, or whether it can introduce a
  case requiring RAT on a pivot (the pivot-based `ADD_STACK_TO_PROOF` calls
  observed in `congruence.c:1631-1670` are suggestive but not confirmed).
- **Injected (non-generator) symmetry breaking**: needs a PR checker before
  it is safe to run silently, or a re-derivation route through the CDCL
  core the way `xor_drat` handles XOR — either is a real project, not a
  wiring task. Until one exists, treat injected SBPs as **out of scope**,
  full stop, the same way cvc5 treats them as incompatible with LFSC/ALF.
- **XOR/Gaussian at the inprocessing (mid-search) level**: the offline
  per-query pattern in `xor_drat.rs` generalizes, but wiring it into a live
  CDCL loop (rather than a whole-query offline route) is unverified new
  work, not a re-use of what exists.
