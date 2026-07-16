# 12 — Elaboration, E-Graphs, and Finite Model Finding

Status: research note. Fills three citation gaps found by the prover-track citation
audit: (1) the Lean 4 elaborator (load-bearing for P6.2/P6.3), (2) egg / equality
saturation *proof production* (load-bearing for P6.3.3), (3) finite model finding
(load-bearing for P6.6).

Every claim below carries a URL. Claims marked **[unverified]** were not traced to a
primary source in this pass and must not be quoted as fact.

---

## 1. The Lean 4 elaborator

### 1.1 Primary sources

| Source | URL |
| --- | --- |
| de Moura & Ullrich, *The Lean 4 Theorem Prover and Programming Language* (CADE-28, 2021) | <https://lean-lang.org/papers/lean4.pdf> · <https://link.springer.com/chapter/10.1007/978-3-030-79876-5_37> |
| de Moura, Avigad, Kong, Roux, *Elaboration in Dependent Type Theory* (2015) | <https://arxiv.org/abs/1505.04324> |
| Ullrich & de Moura, *Beyond Notations: Hygienic Macro Expansion for Theorem Proving Languages* (IJCAR 2020; LMCS 18(2):1, 2022) | <https://arxiv.org/pdf/2001.10490> |
| Ullrich & de Moura, *'do' Unchained: Embracing Local Imperativity in a Purely Functional Language* (ICFP 2022) | <https://lean-lang.org/papers/do.pdf> |
| Selsam, Ullrich, de Moura, *Tabled Typeclass Resolution* | <https://arxiv.org/abs/2001.04301> |
| Ullrich, *An Extensible Theorem Proving Frontend* (PhD thesis, KIT, 2023; DOI 10.5445/IR/1000161074) | <https://publikationen.bibliothek.kit.edu/1000161074> |
| Lean 4 `MetavarContext.lean` (the delayed-assignment design doc, in-source) | <https://github.com/leanprover/lean4/blob/master/src/Lean/MetavarContext.lean> |
| Lean 4 `Elab/Term.lean` (postponement, synthesis loop) | <https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Term.lean> |

Yes, the thesis exists: Sebastian Ullrich, *An Extensible Theorem Proving Frontend*,
KIT 2023 (<https://publikationen.bibliothek.kit.edu/1000161074>). Its abstract frames
the contribution as "an expressive macro system" covering "syntax transformations" and
**"type-aware elaboration"**, plus "a novel hygiene algorithm inspired by that of the
Lisp-family language Racket but custom-built for ITPs".

### 1.2 What the elaborator does, per its authors

The CADE-28 system description positions Lean 4 as "fully extensible: users can modify
and extend the parser, elaborator, tactics, decision procedures, pretty printer, and
code generator" (<https://lean-lang.org/papers/lean4.pdf>). The elaborator's job is
stated most directly in the 2015 paper: it turns partial, ambiguous user input into
fully elaborated CIC terms, supporting "higher-order unification, type class inference,
ad hoc overloading, insertion of coercions, the use of tactics, and the computational
reduction of terms" — and the authors note "the interactions between these components
are subtle and complex" (<https://arxiv.org/abs/1505.04324>).

**Metavariable context and delayed assignment.** The authoritative description is the
header of `src/Lean/MetavarContext.lean`
(<https://github.com/leanprover/lean4/blob/master/src/Lean/MetavarContext.lean>). The
metavariable context stores declarations and assignments for metavariables shared by
elaboration, unification, and typeclass resolution. The motivating problem for *delayed*
assignment: abstracting a free variable `x` out of a term containing `?m` where `?m`'s
local context includes `x` would produce an ill-formed `fun x => t[?m]` once `?m` is
later assigned a term mentioning `x`. The fix is to create an auxiliary `?n` over an
adjusted local context, assign `?m := ?n x`, and emit `fun x => t[?n x]` — in the file's
words, *"we are essentially using the pair 'delayed assignment + application' to
implement a delayed substitution."*

**Metavariable kinds** (same file) control who may solve what:

- **natural** — `isDefEq` may assign freely.
- **synthetic** — `isDefEq` avoids assigning; used for typeclass resolution.
- **syntheticOpaque** — never assigned by `isDefEq`; these represent *unsolved subgoals*.

Plus a **depth** discipline: "Metavariables from depth N+1 must be fully assigned before
we return to level N", and "TC should not assign metavariables created by the
elaborator, simp, tactic framework, and outer TC problems". This is the mechanism that
keeps a nested unification/TC subproblem from silently committing the parent's holes.

**Postponement / elaboration order.** Term elaboration is not a single pass: elaboration
problems that cannot yet be decided (overload choices, coercions, TC goals, `_`s whose
expected type is not yet known) are *postponed* and retried by a synthesis loop as the
metavariable context becomes more instantiated; the implementation lives in
`Lean/Elab/Term.lean`
(<https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Term.lean>). The 2015
paper is the design rationale for this "balance efficiency and usability" ordering
(<https://arxiv.org/abs/1505.04324>).

**Monad stack.** `MetaM` (metavariables + local contexts + defeq/whnf),
`TermElabM` (syntax → `Expr`, postponement, TC synthesis queue), `TacticM` (a goal list
over `TermElabM`) — layered, each adding state to the one below. The paper-level
citation for the design is the thesis
(<https://publikationen.bibliothek.kit.edu/1000161074>); the crisp per-monad breakdown
is the community *Metaprogramming in Lean 4* book
(<https://leanprover-community.github.io/lean4-metaprogramming-book/>) — secondary, not
primary.

**Hygiene.** *Beyond Notations* (<https://arxiv.org/pdf/2001.10490>) is the primary
source: a Racket-inspired, capture-avoiding macro system custom-built for ITPs, solving
"accidental name capture" in the Lean 3 tactic language and the "restrictive syntax
sugar" problem simultaneously. Hygiene here is a property of *syntax objects with scope
annotations* — it exists because there is a surface syntax and users write macros over
it.

**Typeclass resolution.** Per CADE-28, Lean's TC resolution "can be viewed as a simple
λ-Prolog interpreter, where the Horn clauses are the user declared instances"; Lean 4
replaced Lean 3's backtracking search with **tabled** resolution using discrimination
trees for indexing, to fix "unnecessary overhead due to the lack of term indexing" and
"exponential running times in the presence of diamonds"
(<https://lean-lang.org/papers/lean4.pdf>, <https://arxiv.org/abs/2001.04301>).

**Unification.** Full higher-order unification is undecidable; Lean, like other
dependently typed elaborators, leans on the **Miller pattern** fragment (`?m x₁ … xₙ`
with distinct bound-variable arguments) where most-general unifiers exist and are
unique, and uses heuristics outside it. The 2015 paper's list explicitly includes
"higher-order unification" (<https://arxiv.org/abs/1505.04324>); the CADE-28 paper's
bibliography cites Miller & Nadathur, *Programming with Higher-Order Logic*
(<https://lean-lang.org/papers/lean4.pdf>, ref. [8]). The precise fragment Lean 4's
`isDefEq` treats as pattern-unifiable, and its heuristics outside it, are **[unverified]**
against a primary text in this pass — the source of truth is `Lean/Meta/ExprDefEq.lean`.

### 1.3 What this implies for axeyum

**The design question: which parts survive if you delete the parser?** Sort the
elaborator's machinery by whether it is about *surface syntax* or about *goal-directed
proof over dependent types*.

**Dies with the parser (Lean-specific surface accident — do not port):**

- **Hygiene / macro expansion.** Hygiene is a solution to name capture in
  *user-written textual macros* (<https://arxiv.org/pdf/2001.10490>). If goals are data
  (de Bruijn-indexed `Expr`s constructed by an agent/tactic API, never re-parsed), there
  is no capture problem to avoid; hygiene's whole problem statement evaporates. Ullrich's
  thesis is a thesis about *the frontend*
  (<https://publikationen.bibliothek.kit.edu/1000161074>) — that is precisely the part we
  are not building.
- **`do` notation / `Syntax` quotations** (<https://lean-lang.org/papers/do.pdf>): an
  ergonomics layer for writing Lean in Lean. Irrelevant to a Rust host.
- **Ad hoc overloading and coercion insertion.** Both exist to disambiguate *what the
  user typed*. An API-constructed goal is already unambiguous. (Coercions may return
  later as a *library* concern; they are not a kernel-adjacent concern.)
- **Notation-driven elaboration order.** Postponement exists partly because token order
  ≠ information order. Some of this survives (below), but the parser-shaped parts do not.

**Survives — this is the actual P6.2 kernel-adjacent core (port it):**

1. **The metavariable context itself.** Goals *are* metavariables. `syntheticOpaque`
   is literally "this is an unsolved subgoal"
   (<https://github.com/leanprover/lean4/blob/master/src/Lean/MetavarContext.lean>).
   A prover with holes needs this data structure regardless of syntax.
2. **Delayed assignment.** This is a *type-theoretic* necessity, not a syntactic one:
   it exists because abstracting a binder over a term with an open metavariable whose
   local context contains that binder is ill-formed. Any tactic that introduces a
   binder around a hole (`intro`, `induction`, anything producing `fun x => ?goal`) hits
   this. **This is the single most important thing to copy from Lean 4, and the least
   obvious.** Getting it wrong is a soundness-adjacent kernel-rejection bug.
3. **Metavariable kinds + depth discipline.** The invariant "metavariables from depth
   N+1 must be fully assigned before we return to level N" and "TC should not assign
   metavariables created by the elaborator, simp, tactic framework, and outer TC
   problems" are what make nested search *composable*. Our P6.3 tactics + P6.2
   unification will need exactly this discipline, or a `simp` subcall will silently
   solve a sibling goal.
4. **Postponement, in its semantic form.** Not "the parser gave me tokens in the wrong
   order" but "this constraint is not yet decidable; retry when the mvar context grows."
   That is the same loop, minus syntax. Keep it.
5. **Higher-order pattern unification.** Needed the moment goals contain applied
   metavariables. Decidable, unique MGUs in the Miller fragment; heuristic outside. This
   is a P6.2 deliverable in its own right.
6. **Typeclass resolution — *if* we adopt typeclasses.** Tabled resolution +
   discrimination trees (<https://arxiv.org/abs/2001.04301>) is the state of the art and
   the diamond-blowup fix. But TC is a *library design* choice; if axeyum's goal layer is
   certificate-first over a fixed theory surface, TC may be deferrable. Discrimination
   trees themselves are *not* deferrable — we need term indexing for `simp` lemma lookup
   anyway.

**Consequence for the track:** P6.2 should be scoped as
*mvar context + delayed assignment + kinds/depth + pattern unification + a postponement
queue* — and explicitly **not** as an elaborator. The 2015 paper
(<https://arxiv.org/abs/1505.04324>) is our design reference for the search-shaped parts;
*Beyond Notations* and the thesis are our reference for what to **skip**. Citing the
thesis in the plan is honest only if we cite it as "the frontend we are deliberately not
building."

---

## 2. egg / equality saturation, and whether it proves anything

### 2.1 Primary sources

| Source | URL |
| --- | --- |
| Willsey, Nandi, Wang, Flatt, Tatlock, Panchekha, *egg: Fast and Extensible Equality Saturation* (POPL 2021) | <https://dl.acm.org/doi/10.1145/3434304> · <https://dl.acm.org/doi/pdf/10.1145/3434304> |
| Tate, Stepp, Tatlock, Lerner, *Equality Saturation: A New Approach to Optimization* (POPL 2009) | <https://dl.acm.org/doi/10.1145/1594834.1480915> |
| Nelson & Oppen, *Fast Decision Procedures Based on Congruence Closure* (JACM 1980) | <https://dl.acm.org/doi/10.1145/322186.322198> |
| Nelson, *Techniques for Program Verification* (PhD thesis, 1980) — the e-graph / congruence closure source | <https://people.eecs.berkeley.edu/~necula/Papers/nelson-thesis.pdf> |
| Flatt, Coward, Willsey, Tatlock, Panchekha, *Small Proofs from Congruence Closure* (FMCAD 2022) | <https://arxiv.org/abs/2209.03398> · <https://arxiv.org/pdf/2209.03398> · <https://www.mwillsey.com/papers/egg-proofs> |
| Detlefs, Nelson, Saxe, *Simplify: A Theorem Prover for Program Checking* (HPL-2003-148; JACM 2005) — proof-producing congruence closure lineage | <https://shiftleft.com/mirrors/www.hpl.hp.com/techreports/2003/HPL-2003-148.html> (HP Labs mirror; the original hpl.hp.com host is dead) · <https://dl.acm.org/doi/10.1145/1066100.1066102> |
| Nieuwenhuis & Oliveras, *Proof-Producing Congruence Closure* (RTA 2005) | <https://link.springer.com/chapter/10.1007/978-3-540-32033-3_33> |
| `egg` `EGraph::explain_equivalence` API docs | <https://docs.rs/egg/latest/egg/struct.EGraph.html#method.explain_equivalence> |

### 2.2 The key question: does egg produce proofs?

**Yes.** egg produces *explanations*: given two expressions in the same e-class,
`explain_equivalence` returns a chain of rewrite steps witnessing their equality. The
feature must be enabled up front (`EGraph::with_explanations_enabled` /
`Runner::with_explanations_enabled`) because it requires recording justifications on
union operations (<https://docs.rs/egg/latest/egg/struct.EGraph.html#method.explain_equivalence>).

**How it works.** It is the congruence-closure proof-forest lineage, not something new:
each `union` is recorded with the rule (or congruence) that justified it, building a
proof forest; explaining `a = b` means walking the forest between them and expanding
congruence edges recursively into sub-proofs. The lineage is Nelson's thesis /
Nelson–Oppen congruence closure
(<https://people.eecs.berkeley.edu/~necula/Papers/nelson-thesis.pdf>,
<https://dl.acm.org/doi/10.1145/322186.322198>), made proof-producing by Simplify
(<https://shiftleft.com/mirrors/www.hpl.hp.com/techreports/2003/HPL-2003-148.html>) and Nieuwenhuis–Oliveras
(<https://link.springer.com/chapter/10.1007/978-3-540-32033-3_33>).

**Soundness / completeness.** Explanations are *sound by construction* (each step is a
recorded rule application or a congruence step), and *complete for the relation the
e-graph actually represents*: if two terms are in the same e-class, an explanation
exists. Note carefully what is **not** claimed: equality saturation itself is not a
decision procedure for equality — an e-graph that fails to saturate says nothing about
disequality. egg's "proof" is a *witness of derivability from the given rewrite set*,
not a proof of a semantic equation, and not a refutation. **[unverified]** whether egg's
explanation checker verifies the produced explanation independently (the paper's framing
is "certifying engine"; treat the produced chain as needing an *external* checker — which
is what we want anyway).

**How big, and what does it cost?** This is the point of *Small Proofs from Congruence
Closure* (FMCAD 2022, <https://arxiv.org/abs/2209.03398>). Its own framing:

- "the problem of generating proofs of minimal size is known to be NP-complete";
- "existing proof minimization algorithms for congruence closure generate unnecessarily
  large proofs and introduce asymptotic overhead over the core congruence closure
  procedure";
- they give an **O(n⁵)** algorithm optimal under a relaxed *proof tree size* metric that
  bounds proof size, and a practical **O(n log n) greedy** algorithm that "generates
  small proofs with no asymptotic overhead";
- implemented in egg, making it "the first certifying equality saturation engine";
- the greedy algorithm "quickly generates substantially smaller proofs than the
  state-of-the-art Z3 SMT solver on a corpus of 3760 benchmarks"
  (<https://www.mwillsey.com/papers/egg-proofs>).

Read that last bullet carefully before quoting it: it is a claim about **proof size**
(smaller than Z3's) and speed of *generating* the explanation on their benchmark set. It
is **not** a claim that egg is a faster solver than Z3, and the "3760 benchmarks" number
is theirs, not ours. **[unverified]** what the absolute proof sizes are and how they
scale on our shapes — that must be measured, not assumed.

**The honest cost model:** enabling explanations is not free — it forces the e-graph to
retain justification data on every union and disables some of the rebuilding/
deduplication freedoms egg's "amortized invariant maintenance" buys
(<https://dl.acm.org/doi/10.1145/3434304>). The magnitude of that slowdown is
**[unverified]** and is a thing to benchmark on `axeyum-egraph` directly.

### 2.3 The contrast: reflection vs. certificate

Rocq's `ring` and `lia`/`micromega` are the *other* answer to "how does a simplifier
justify itself":

- `ring` is **proof by reflection**: normalize both sides with a *verified-in-Rocq*
  normalizer over a reified syntax, then close the goal by `Reflexivity`/computation.
  The proof term is tiny and constant-ish; the trust is in the once-and-for-all
  correctness proof of the normalizer, and the cost is moved into kernel *conversion*
  (<https://rocq-prover.org/doc/master/refman/addendum/ring.html>).
- `lia`/`nia`/`psatz` (Micromega) is **certificate-based**: an untrusted oracle
  (Simplex / Positivstellensatz witness search) finds a certificate, and a
  reflective *checker* verifies it
  (<https://rocq-prover.org/doc/master/refman/addendum/micromega.html>). This is
  literally axeyum's "untrusted fast search, trusted small checking" split, and it is
  the closest existing analogue to what P6 is.

### 2.4 What this implies for axeyum

**P6.3.3's "simp must justify itself" is *cheap in kind, uncertain in magnitude*.**

1. **The mechanism exists and is the right one.** We do not need to invent
   proof-producing congruence closure; egg already implements the FMCAD 2022 greedy
   algorithm with *no asymptotic overhead* over the core procedure
   (<https://arxiv.org/abs/2209.03398>). If `axeyum-egraph` follows egg's design, proof
   production is a *retention* problem (keep the justification on every union), not a
   research problem. That answers the plan's open question: **cheap, in the algorithmic
   sense.**
2. **But the explanation is not a kernel proof.** egg gives a chain of *rewrite-rule
   applications*. To land in `axeyum-lean-kernel` each step must be replayed as a
   kernel-checkable equality — i.e. each simp lemma must be a *theorem in the
   environment*, and the chain becomes a `Eq.trans`/congruence spine. The work is in the
   **step→kernel-term lifting**, not in getting the chain out of the e-graph. Size the
   task there.
3. **Explanation size is the risk, and it is measurable now.** NP-complete to minimize
   (<https://arxiv.org/abs/2209.03398>); greedy is good but unbounded on adversarial
   shapes. Before committing P6.3.3, measure explanation length on real goals with
   explanations enabled, and measure the *slowdown* from enabling them. Both numbers are
   currently **[unverified]** for our workloads.
4. **Keep the reflection escape hatch.** For arithmetic normalization specifically, the
   Rocq experience says a *reflective, verified* normalizer beats a per-step certificate
   chain by orders of magnitude in proof size
   (<https://rocq-prover.org/doc/master/refman/addendum/ring.html>). If our kernel gets a
   usable evaluator, `ring`-style reflection is the right long-run answer for algebra and
   e-graph explanations are the right answer for *open-ended, user-extensible* rewriting.
   These are complementary, not competing; do not let P6.3.3 foreclose the reflective
   route.
5. **Micromega is the template for the whole track.** `lia` = untrusted search +
   reflective checker + certificate. That is our identity sentence with different nouns
   (<https://rocq-prover.org/doc/master/refman/addendum/micromega.html>). Cite it in the
   design doc as prior art for the seam, not just as a tactic.

---

## 3. Finite model finding

### 3.1 Primary sources

| Source | URL |
| --- | --- |
| Reynolds, Tinelli, Goel, Krstić, *Finite Model Finding in SMT* (CAV 2013) | <https://link.springer.com/chapter/10.1007/978-3-642-39799-8_42> |
| Reynolds, Tinelli, Goel, Krstić, Deters, Barrett, *Quantifier Instantiation Techniques for Finite Model Finding in SMT* (CADE 2013) | <https://homepage.cs.uiowa.edu/~tinelli/papers/ReyEtAl-CADE-13.pdf> |
| Reynolds, Tinelli, de Moura, *Finding Conflicting Instances of Quantified Formulas in SMT* (FMCAD 2014, pp. 195–202) | <https://www.cs.utexas.edu/~hunt/fmcad/fmcad14/proceedings/31_reynolds.pdf> · <https://homepage.divms.uiowa.edu/~ajreynol/fmcad14.pdf> · <https://dblp.org/rec/conf/fmcad/ReynoldsTM14.html> |
| Reynolds, Blanchette, Cruanes, Tinelli, *Model Finding for Recursive Functions in SMT* (IJCAR 2016 / JAR) | <https://link.springer.com/chapter/10.1007/978-3-319-40229-1_10> |
| Reynolds, Tinelli, Barrett, *Constraint Solving for Finite Model Finding in SMT Solvers* (TPLP 2017 — the extended journal version; **the one to read**) | <https://arxiv.org/abs/1706.00096> · <https://arxiv.org/pdf/1706.00096> |
| Claessen & Sörensson, *New Techniques that Improve MACE-style Finite Model Finding* (CADE-19 Workshop on Model Computation, 2003) — Paradox | <http://fitelson.org/paradox.pdf> · <https://www.semanticscholar.org/paper/e139e0d66116020530923b514607300523c7e8c8> |
| McCune, *Mace4 Reference Manual and Guide* (2003) | <https://www.cs.unm.edu/~mccune/prover9/mace4.pdf> |
| Piskac / Ge & de Moura, *Complete Instantiation for Quantified Formulas in SMT* (CAV 2009) — the "essentially uninterpreted" completeness lineage | <https://link.springer.com/chapter/10.1007/978-3-642-02658-4_25> |
| cvc5 `--finite-model-find` option docs | <https://cvc5.github.io/docs/latest/options.html> |
| Padon et al., *Paxos Made EPR* (OOPSLA 2017) — EPR fragment, finite model property, and the ∀∃-Skolemization trap | <https://arxiv.org/pdf/1710.07191> |

### 3.2 How FMF actually works

The problem statement (TPLP 2017, <https://arxiv.org/pdf/1706.00096>): "techniques for
dealing with quantified formulas in SMT are generally incomplete, forcing SMT solvers to
report 'unknown' when they fail to prove the unsatisfiability of a formula with
quantifiers. This inability to return counter-models limits their usefulness." Because
first-order logic is undecidable, "there are no automated methods for finding arbitrary
models", so they "focus on **finite** models, which can be represented symbolically and
enumerated."

The architecture is a loop, `FM-Solve_H(F, A)` (Fig. 3 of
<https://arxiv.org/pdf/1706.00096>), where `F` is ground clauses and `A` maps proxy
literals to quantified formulas (`a ⇔ ∀x φ`):

1. **Find a satisfying assignment `M` for `F`. If none is found, return `unsat`.**
2. **Construct a Σ-interpretation `M` satisfying `M`, considering only interpretations
   that interpret the uninterpreted sorts as *finite* sets.** Compute `V`, a minimal set
   of terms denoting every element of each uninterpreted sort.
3. **For each active `∀x φ`, add instances `φσ` for substitutions `σ: x → V` chosen by
   heuristic `H`. If every `I_x` was empty, return `sat`; otherwise go to 1.**

The three components:

- **Sort cardinality constraints.** The paper introduces the theory **FCC** = EUF with
  finite cardinality constraints, with an atom `card_{S,k}` satisfied exactly by models
  interpreting sort `S` as a set of cardinality **at most** `k`. FCC-satisfiability of
  literal sets is decidable (Prop. 2); the QF satisfiability problem is NP-complete; the
  solver works on a *region graph* of the congruence closure's equivalence-class
  representatives with disequality edges, and finding a `k`-bounded model is graph
  colouring in disguise ("represent the set of k colors as a sort C ... a cardinality
  constraint on C is encoded by `card_{C,k}`").
- **Incremental cardinality search.** The `card_{S,k}` literals are asserted as
  *decisions inside DPLL(T)*, not as top-level assumptions. The strategy
  `fixed-cardinality check_FCC` "ensures that upper bounds are incrementally established
  for all uninterpreted sorts": try `k = 1`; when the bound is refuted, the SAT engine
  backtracks and the search moves to `k+1`. This is the minimal-model search.
- **Model-based quantifier instantiation over the finite domain.** Because the candidate
  model is finite and symbolically represented (Σ-maps), the heuristic can "identify, and
  ignore, entire sets of instances that do not need to be considered", and can generate
  one *representative* instance for many.

The MACE/Paradox ancestry: Paradox and Mace4 do finite model finding by *reduction to
SAT* — fix a domain size `n`, ground the problem over `n` constants, blast to
propositional logic, increment `n`
(<http://fitelson.org/paradox.pdf>,
<https://www.cs.unm.edu/~mccune/prover9/mace4.pdf>). The TPLP paper explicitly
distinguishes itself: "Most traditional finite model finders for quantified formulas are
based on a reduction to a decidable logic, propositional logic or some decidable
fragments of [first-order logic]"; cvc5's method instead does **not** introduce domain
constants for the free sorts and is integrated into DPLL(T) via the FCC solver
(<https://arxiv.org/pdf/1706.00096>, <https://link.springer.com/chapter/10.1007/978-3-642-39799-8_42>).

### 3.3 The crux: when is carrier-bounding sound for `unsat`?

**Our stated belief was: "sound for `unsat` only inside EPR/Bernays–Schönfinkel."
That belief is *partly right and importantly wrong about FMF*.** Both halves need
separating.

**(a) Hard carrier-bounding — what our QF_UF route does.** If you *assert* `|S| ≤ k` as
a top-level constraint and derive `unsat`, you have proved "no model with `|S| ≤ k`",
which is **not** `unsat` of the original problem — unless the fragment has the **finite
model property with a computable bound**, and `k` meets that bound.

- The EPR / Bernays–Schönfinkel–Ramsey class — prenex `∃*∀*`, relational vocabulary
  (constants and relations, **no function symbols**) — has the finite model property:
  "a satisfiable formula is guaranteed to have a finite model. The size of this model is
  bounded by the total number of existential quantifiers and constants in the formula"
  (<https://arxiv.org/pdf/1710.07191>). So inside EPR, bounding the carrier at that
  *specific computed* bound and getting `unsat` **is** sound for the original — because
  every model can be collapsed to one of that size.
- Bounding *below* that number is sound for `sat` only. A model found under a small
  bound is a real model (the bound is an extra constraint; satisfying a
  strengthened formula satisfies the original). `unsat` under a small bound is *not* a
  refutation, only "no small model."
- **The ∀∃ trap is real, and confirmed.** EPR forbids function symbols; Skolemizing
  `∀x ∃y. φ` introduces a Skolem *function* `f(x)`, which leaves EPR and destroys the
  guarantee. This is exactly the problem *Paxos Made EPR* exists to work around: the
  paper's whole contribution is rewriting specifications to eliminate ∀∃ quantifier
  alternation so the verification conditions stay in EPR
  (<https://arxiv.org/pdf/1710.07191>). **So: our belief about the ∀∃/Skolemization trap
  is verified.** (Note the direction: `∃*∀*` prenex Skolemizes to *constants*, which stay
  in EPR; it is `∀∃` — i.e. `∀*∃*`, or a `∃` under a `∀` after negation — that produces a
  function symbol and leaves the class.)

**(b) FMF's `unsat` — and here our belief is *refuted as a description of FMF*.**
cvc5's FMF does **not** hard-bound the carrier, so its `unsat` does not depend on the
finite model property at all, and is sound for **arbitrary** first-order formulas — no
EPR needed. Theorem 2.1 of the TPLP paper (<https://arxiv.org/pdf/1706.00096>):

> "If the method for finding satisfying assignments `M` for `F` in Step 1 is sound, then
> the procedure `FM-Solve_H` returns `unsat` only if `F ∪ A` is `T`-unsatisfiable."

with the proof: "when the procedure returns `unsat`, we have that `F` is
`T`-unsatisfiable. Since the formulas added to `F` and `A` in Step 3 **preserve
satisfiability**, we have that our input is `T`-unsatisfiable as well."

Read the mechanism: `unsat` is returned **from Step 1**, on the *ground* clause set `F`,
which contains only the original ground clauses plus **instances** `φσ` of quantified
formulas. Ground instances of a universally quantified formula are logical
*consequences* — adding them can never turn a satisfiable problem unsatisfiable. The
cardinality literals `card_{S,k}` live in the DPLL(T) *assignment*, are backtrackable
decisions, and the FCC solver's job when the bound fails is to let the search go to
`k+1`, not to report `unsat` (Fig. 4: it returns `unsat` for the *literal set under those
decisions*, which is a T-conflict driving backtracking, not a top-level answer). The
carrier bound is a **search strategy for enumerating candidate models and choosing which
instances to generate**, not a soundness-bearing assumption.

**Correspondingly, symmetrically:** FMF's `sat` is sound only if the heuristic `H` is
model-sound — Theorem 2.2: "If for all inputs, `H(M, ∀x φ)` returns the empty set only if
`M ⊨ ∀x φ`, then the procedure returns `sat` only if `F ∪ A` is `T`-satisfiable"
(<https://arxiv.org/pdf/1706.00096>). i.e. you may only answer `sat` when you have
*checked* the candidate finite model against every active quantified formula.

**So: is our carrier-bounding the same technique as FMF, or a weaker cousin?**
**A weaker cousin — and a differently-shaped one.**

| | axeyum QF_UF carrier-bounding | cvc5 FMF |
| --- | --- | --- |
| Bound is | a hard, top-level constraint | a backtrackable DPLL(T) decision (`card_{S,k}`) |
| `sat` sound? | yes (bound only strengthens) | yes, *if* the model is checked against all quantifiers (Thm 2.2) |
| `unsat` sound? | **only** with the finite model property + a correct computed bound (EPR) | **yes, unconditionally** — comes from ground instances, not the bound (Thm 2.1) |
| Bound grows? | no (fixed) | yes (incremental minimal-model search) |
| What the bound buys | tractable finite encoding | a finite `V` to instantiate over, and small models first |

Our route is essentially **MACE/Paradox-style** (fix `n`, ground, blast to SAT) minus the
increment loop — which is the *ancestor* technique the CAV/TPLP papers explicitly
contrast themselves against
(<http://fitelson.org/paradox.pdf>,
<https://arxiv.org/pdf/1706.00096>). The 54–67% is therefore a **`sat`-shaped**
achievement wearing a percentage; **[unverified — must be traced]** whether any `unsat`
in that 54–67% was claimed under a hard bound outside EPR. **If it was, it is a wrong
`unsat`.** This is the highest-priority audit item this note produces.

### 3.4 Does FMF help on `unsat` at all?

**Yes — but indirectly, and it is not what it is for.** Three points, in order of
confidence:

1. **FMF's `unsat` is sound** (Thm 2.1, above) — so an FMF run may legitimately answer
   `unsat`. It is not a `sat`-only mode.
2. **The mechanism by which it finds `unsat`** is that the model-based instantiation
   loop is a *fair-ish enumeration of ground instances*: each round the candidate model
   `M` fails some quantified formula, the heuristic emits the instance witnessing the
   failure, and that instance is added to `F`. If the problem is unsatisfiable, this
   grinds toward the refuting instance set. Because FMF searches *minimal* models first,
   `V` is small, so the instances it generates are few and highly targeted — which on
   small-signature puzzle problems can find the refutation faster than E-matching, which
   generates instances triggered by syntactic patterns rather than by model failure.
   (The same "instantiate where the candidate model fails" idea is the basis of
   conflict-based instantiation, <https://www.cs.utexas.edu/~hunt/fmcad/fmcad14/proceedings/31_reynolds.pdf>.)
3. **It is nonetheless a `sat`-oriented mode**, and the papers say so — the motivation is
   "counter-models", and FMF is generally *worse* than E-matching / MBQI on
   `unsat`-heavy benchmark families. **[unverified]** in specific numbers; do not quote a
   figure.

**On our one `unsat` fmf goal, PUZ001+1 (Dreadbury Mansion).** The
`; COMMAND-LINE: --finite-model-find` header is a cvc5 **regression-test annotation**
recording the configuration under which the test is run — it is an instruction to the
test harness, not a claim that FMF is *required*. Dreadbury Mansion is a tiny,
finite-signature, `unsat` puzzle; it is exactly the shape where minimal-model
instantiation finds the refutation immediately, and it is plausibly also solvable
without the flag. **[unverified]** whether cvc5 solves PUZ001+1 without
`--finite-model-find`; that is a 30-second experiment we should run rather than
speculate about. Also note PUZ001+1 is TPTP's Dreadbury with **∃** in the axioms — check
whether it is EPR at all before assuming a bounded route is sound on it.

### 3.5 What this implies for axeyum

1. **P6.6 must not report `unsat` from a hard carrier bound outside EPR.** This is a
   soundness rule, not a quality rule, and it belongs in the plan as a hard gate with a
   soundness-negative test: construct a formula that is `unsat` under `|S| ≤ k` and `sat`
   at `|S| = k+1` (trivially: `k+1` pairwise-distinct constants plus a `∀`-axiom that
   only a larger carrier satisfies), assert the harness answers `unknown`, not `unsat`.
   Per CLAUDE.md's rule on underspecified operators, the *bounded carrier* is exactly
   such a degenerate axis and needs a generator that deliberately emits it.
2. **The cheap, correct upgrade is the increment loop.** Going from "fixed bound" to
   "incremental minimal-model search with a backtrackable bound" is what converts our
   weaker cousin into the real technique — and it is what makes `unsat` sound
   unconditionally, because the refutation then comes from *instances*, not the bound
   (<https://arxiv.org/pdf/1706.00096>, Thm 2.1). **Land the loop before quoting any
   `unsat` number from the bounded route.**
3. **Answer `sat` only after checking the model.** Thm 2.2 is a checkable obligation and
   it matches our existing house rule ("every `sat` result must be checkable by
   evaluating the original term against the lifted model"). For quantified UF, "evaluate
   the model" means evaluating each `∀x φ` over the finite carrier — which is *possible
   precisely because the carrier is finite*. This is the strongest argument for the
   finite-model route in our stack: **it is the only quantified route where `sat` is
   self-checking.** Say that in the plan; it is a better justification than the 54–67%.
4. **We can run EPR detection cheaply, and it pays for itself.** A syntactic check
   (prenex `∃*∀*`, no non-constant function symbols after Skolemization) tells us when
   the hard bound *is* sound for `unsat` and what the bound must be (existentials +
   constants, <https://arxiv.org/pdf/1710.07191>). Inside EPR: `unsat` is licensed at the
   computed bound. Outside: `sat` only. That is a small, well-defined P6.6 deliverable
   and it converts a hazard into a capability.
5. **The FCC solver is a real, portable design.** EUF + cardinality constraints, decided
   over the congruence closure's region graph, integrated as a DPLL(T) theory
   (<https://arxiv.org/pdf/1706.00096>). We already have congruence-closure-shaped
   machinery in `axeyum-egraph`; the FCC solver is a plausible next theory rather than a
   rewrite. Note NP-hardness (graph colouring) up front so nobody is surprised.
6. **`--finite-model-find` in a corpus header is provenance, not physics.** Three of five
   quantified-UF goals carrying the flag tells us how cvc5's *regression suite* runs them.
   It does not tell us the goals require FMF, and it must not be cited as evidence that
   FMF is the only route. Re-run them both ways and record the actual data.
7. **Certificate story.** FMF `sat` produces a finite model — a genuinely checkable
   artifact, and one our evidence formats can carry. FMF `unsat` produces an
   *instantiation set*; a kernel proof would be the instance set plus the ground
   refutation (which our SAT route can already emit as DRAT). That is a clean two-layer
   certificate and it fits the track's certificate-first identity. Instance-set +
   ground-proof is the same shape as Alethe's quantifier instantiation steps — see
   ADR-0166 for the Alethe target reassessment.
