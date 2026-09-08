# Term rewriting / simplification infrastructure — pipeline survey 2026-09

Scope: the rewrite/simplify layer that runs before query planning and solving.
Ours is `crates/axeyum-rewrite/` over the typed IR in `crates/axeyum-ir/`.
Sources: local shallow clones in `references/z3` and `references/cvc5`
(file:line citations, tag `[C]`), the egg (egraphs-good/egg) library docs and
POPL 2021 paper (tag `[P]`/`[W]`), the RARE/Alethe proof-reconstruction paper
cited directly from cvc5 source, and web search for context not available
locally (tag `[W]`). `[I]` marks my inference. Absence claims below were
checked by reading the actual module, not by grep-for-name; where I did not
verify something I say so.

## 0. Ranked findings — value across all 12 divisions

Ranked by "helps every theory downstream" first, theory-specific tricks last.
**G** = general (division-independent), **T** = theory-specific.

1. **[G] A rewrite rule set should be data, not Rust match arms.** cvc5's
   RARE rules (`(define-rule name (bindings) lhs rhs)`, §3 below) are literal
   S-expression facts consumed by one generic matcher/applier, checked sound
   once, and reused by both the fast rewriter and the proof reconstructor. Our
   `axeyum-rewrite::canonical::rewrite_app` (5290-line file) has ~90 rules but
   every one is a Rust `match` arm gated by `enabled.contains(RULE_ID)`
   (`crates/axeyum-rewrite/src/canonical.rs:1335-2707`) — the manifest
   (`crates/axeyum-rewrite/src/lib.rs:220-320`) carries only metadata
   (preservation class, projection, test route), never the transform itself.
   This is the single highest-leverage structural gap: it blocks a declarative
   rule table, third-party rule contribution, and automatic proof
   reconstruction from a rule database (§5/§7 below). **[I]**

2. **[G] We have no rewrite-step proof/certificate at all.** Verified: no
   `proof`/`Proof`/`certificate` symbol anywhere in `canonical.rs`. Z3
   optionally builds a proof object inline during rewriting
   (`m_pr`/`mk_congruence`/`mk_rewrite`/`mk_transitivity`,
   `references/z3/src/ast/rewriter/rewriter_def.h:296-370`); cvc5 does *not*
   log proofs during the fast rewrite — it reconstructs them lazily,
   on-demand, from a separate proof-reconstruction module keyed off the same
   rule database (§5). Either shape is compatible with this repo's "kernel
   checks a small trusted core" story; the *replay-and-reconstruct* shape
   (cvc5's) is cheaper for the hot path and is the one directly reusable here,
   since our `RewriteRule`/`RewriteRuleId` metadata already gives every rule a
   stable name to reconstruct against.

3. **[G] Denotational precondition sampling is a feature Z3/cvc5 don't have
   at runtime, and it is worth keeping.** `PreconditionCheck`
   (`crates/axeyum-rewrite/src/canonical.rs:987-1104`) evaluates every
   committed rewrite on N sampled assignments and refuses the commit if the
   before/after values disagree — Z3 and cvc5 rely on offline fuzzing/testing
   for this, not a runtime guard. This is real, working soundness
   infrastructure; the report below treats it as a strength to preserve, not
   a gap.

4. **[G] Cost control: local fuel exists; a documented AC-rebuild-width cap
   exists; there is no rewriter-wide step/resource budget analogous to cvc5's
   `ResourceManager::spendResource(Resource::RewriteStep)`
   (`references/cvc5/src/theory/rewriter.cpp:248`).** Our `canonicalize_root`
   does one bottom-up pass with a *per-node* local-rewrite-chain cap
   (`DEFAULT_LOCAL_REWRITE_FUEL = 8`,
   `crates/axeyum-rewrite/src/canonical.rs:112,1171-1263`), and AC flattening
   is capped at 64 operands with a measured, cited rationale
   (`AC_REBUILD_MAX_OPERANDS`, `canonical.rs:20-39`). `solve_eqs` has its own
   separate 5M-node-visit fuel (`solve_eqs.rs:36-42`). There is no single
   pass-wide node/step counter shared by the whole canonicalizer the way
   Z3/cvc5 spend one resource unit per rewrite step against a global budget —
   worth naming as a design decision, not necessarily a defect, since our
   passes are each individually bounded and the overall pipeline is a fixed
   sequence of bounded passes rather than one recursive rewriter.

5. **[G] Boolean-structure simplification (AND/OR flattening with duplicate
   and complementary-literal detection = "skeleton"/pure-literal reasoning)
   is present in Z3 (`mk_nflat_and_core`,
   `references/z3/src/ast/rewriter/bool_rewriter.cpp:90-153`) and is
   **absent** in ours beyond pairwise identity/annihilator/idempotent rules**
   (`BOOL_AND_IDENTITY`/`ANNIHILATOR`/`IDEMPOTENT`,
   `canonical.rs:1850-1878`). Z3's AC-flatten step marks every positive and
   negative literal seen while flattening an n-ary AND/OR and short-circuits
   to `false`/`true` the moment a literal and its negation both appear, or
   dedupes a repeat — this is a genuinely general, cheap, always-on win we do
   not have at n-ary scope (we only catch it pairwise, and only after our
   generic AC-sort-and-rebuild, which does not special-case complementary
   pairs at all). Verified absent by reading `is_ac`/`flatten_ac_bounded`
   (`canonical.rs:1569-1650`) — flattening sorts and dedupes-by-position only
   for the non-idempotent numeric case (`fold_bv_add_constant_chain`); no
   contradiction/tautology short-circuit exists for `BoolAnd`/`BoolOr` at
   n-ary width.

6. **[G] ITE lifting through non-Boolean operators (hoisting a shared `ite`
   out of an arithmetic/bit-vector operator so both branches can be folded
   together) exists in Z3's `poly_rewriter` (`hoist_ite`/`apply_hoist`,
   `references/z3/src/ast/rewriter/poly_rewriter.h:84-85`) and is **absent**
   here.** We only have ITE-on-ITE and ITE-with-constant-condition collapse
   (`rewrite_ite`, `canonical.rs:2369-2422`); we do not push/pull `ite` across
   `bvadd`/`bvmul`/etc. `[I]` this is theory-general in effect (helps
   BV/LIA/LRA alike) but the mechanism is theory-specific per operator.

7. **[T, but broadly reusable] `solve_eqs`/`propagate_values`/
   `elim_unconstrained` already implement three of Z3's highest-value
   pre-bit-blast passes** (`solve_eqs.rs`, `propagate_values.rs`,
   `elim_unconstrained.rs`), each explicitly modeled on Z3's `solve_eqs` and
   `elim_unconstr` tactics, each **model-sound** via a shared
   `ModelReconstructionTrail` (`crates/axeyum-rewrite/src/reconstruct.rs`).
   This is strong, already-built infrastructure; nothing to add here except
   noting Z3's analogous quantifier-scoped version (`der.cpp`, destructive
   equality resolution *inside* a quantifier body) has no counterpart in our
   `quantifiers.rs`, which does trigger-based and enumerative instantiation
   but not DER-style bound-variable elimination inside a `forall`/`exists`
   body before instantiation.

8. **[T] Global AC-sharing maximization (Z3's `maximize_ac_sharing`,
   `references/z3/src/ast/rewriter/maximize_ac_sharing.h`) is a different,
   heavier design point than our approach and is not obviously worth porting.**
   Z3 caches `(decl, arg1, arg2)` pairs already built *elsewhere in the whole
   formula* and greedily re-associates new AC nodes to reuse them — an
   order-of-traversal-dependent heuristic the file's own doc comment admits is
   "opportunistic... no guarantee of optimal." We instead flatten + sort by
   `TermId` + rebuild balanced (`flatten_ac`/`rebuild_balanced`,
   `canonical.rs:1622-1746`), which gives a *canonical* (traversal-order
   independent) form — strictly better for hash-consing identical operand
   multisets across the DAG, weaker at reusing partial sums that were never
   flattened together in the first place. The report's recommendation: keep
   ours; it is simpler and already has a measured cap
   (`AC_REBUILD_MAX_OPERANDS`) with real corpus evidence behind the number.

9. **[T, quantifiers] E-matching (Z3/cvc5's classic trigger-based quantifier
   instantiation, de Moura & Bjørner CADE 2007) has a real counterpart here**:
   `axeyum-egraph`'s `EMatchIndex`/`ematch`/`ematch_many_indexed`
   (`crates/axeyum-egraph/src/lib.rs:166-656`), consumed by
   `instantiate_with_triggers` (`crates/axeyum-rewrite/src/quantifiers.rs:472-` )
   for trigger-based universal instantiation. **This is genuine congruence-
   closure e-matching, not equality saturation** — see §9 below for the
   distinction. `axeyum-rewrite` itself does not depend on `axeyum-egraph`
   (checked `Cargo.toml`: `axeyum-rewrite`'s only dependency is `axeyum-ir`),
   so the term-rewriting/canonicalization layer and the e-matching/EUF layer
   are architecturally separate; e-matching is used only for quantifier
   instantiation, never for general term rewriting.

10. **[G, speculative] Equality saturation (egg-style) is not something to
    add to the core canonicalizer.** Per the egg paper and follow-up
    literature (§2), naive equality saturation with AC rules blows up
    superlinearly/exponentially — exactly the operand-explosion problem our
    `AC_REBUILD_MAX_OPERANDS` cap and Z3's flat/sorted-rebuild both exist to
    avoid by committing to ONE canonical form instead of keeping all
    permutations live. Full equality saturation is a good fit for a
    *bounded, offline* search over a small subterm (e.g. finding an
    alternative encoding for one hot subexpression before bit-blasting) but a
    poor fit for whole-query, always-on simplification — no evidence turned up
    of a production SMT solver using saturation as its primary
    pre-bit-blast simplifier; Z3 and cvc5 both use ordinary single-pass
    rewriting to a syntactic fixpoint, not saturation, for this stage. This
    is my own synthesis of the literature (`[I]`), not a claim read from a
    paper.

## 1. How production solvers structure a rewriter

### Z3 (`src/ast/rewriter/`)

**Core template + status protocol.** The shared driver is `rewriter_tpl<Config>`
(`references/z3/src/ast/rewriter/rewriter_def.h`), templated on a `Config` that
supplies `reduce_app(func_decl*, num_args, args, result, proof)`. A theory
plugs in by returning a `br_status`:

```
enum br_status {
    BR_REWRITE1, BR_REWRITE2, BR_REWRITE3, BR_REWRITE_FULL, // rewrite result,
                                                              // bounded by depth
    BR_DONE,      // fully simplified, stop
    BR_FAILED     // no builtin rewrite available
};
```
`[C]` `references/z3/src/ast/rewriter/rewriter_types.h:26-34`. `BR_REWRITE1..3`
tell the driver to re-descend into the *result* it just produced, up to that
many levels (`RW_UNBOUNDED_DEPTH = 3`), so a single `reduce_app` call can
trigger a small bounded cascade of further simplification without the caller
looping explicitly
(`references/z3/src/ast/rewriter/rewriter_def.h:354-370`). This is the same
shape as our `local_fuel` reconsideration loop
(`canonicalize_root_bounded`, `canonical.rs:1171-1263`), independently arrived
at — a rewritten node is re-offered to the rule dispatcher a bounded number of
times before the driver moves on, rather than looping to unbounded fixpoint.

**Traversal.** `main_loop`/`process_app` (`rewriter_def.h:267-420,718-`) is an
explicit worklist over a `frame` stack, not C++ recursion — avoids stack
overflow on deep terms, same reason our `canonicalize_root_bounded` uses an
explicit `Vec` stack instead of recursion (`canonical.rs:1178`). Traversal is
bottom-up: children are visited and pushed onto a result stack before the
parent's `reduce_app` runs (`rewriter_def.h:267-278`).

**Caching.** `must_cache(t)` gates memoization to shared, non-root,
non-constant applications: `t->get_ref_count() > 1 && t != m_root && (is_app
&& num_args>0 || is_quantifier)` (`references/z3/src/ast/rewriter/rewriter.h:69-74`).
So single-use subterms are *not* memoized — a deliberate memory/time tradeoff,
narrower than our unconditional `HashMap<TermId, TermId>` memo
(`canonical.rs:1155,1176`) which memoizes every visited node. `[I]` ours is
simpler and correct because our arena is already hash-consed (structurally
equal terms share one `TermId` — `crates/axeyum-ir/src/arena.rs:1-44`), so the
memo table size is bounded by the DAG's node count either way; Z3's ref-count
gate is presumably tuned for its own AST manager's ref-counting.

**`mk_simplified_app`** (`references/z3/src/ast/rewriter/mk_simplified_app.cpp`)
is the **always-on, cheap, smart-constructor tier**: dispatched by
`family_id` to `bool_rewriter`/`arith_rewriter`/`bv_rewriter`/etc's
`mk_app_core`, called every time the AST manager builds a node (not just
during an explicit "simplify" pass). Confirms the two-tier design the task
description asks about: local per-node builtin simplification (`mk_*_core`,
`br_status`) is shared code used both by ordinary term construction *and* by
the full `rewriter_tpl` walk — there is one rule implementation, invoked from
two call sites `[C]`.

**Concrete rules** — `bool_rewriter.cpp`:
- AND/OR n-ary flattening with **duplicate and complementary-literal
  detection** using `expr_fast_mark1`/`mark2` bitsets over the flattened
  operand list; a positive and negative mark on the same atom short-circuits
  the whole conjunction/disjunction to `false`/`true`
  (`mk_nflat_and_core`, `bool_rewriter.cpp:90-153`) — the "skeleton"/pure-
  literal reasoning the task asked about.
- ITE simplification (`mk_ite_core`, `bool_rewriter.cpp:917-` — ~15 named
  cases): condition negation swap, nested-same-condition collapse
  (`(ite c (ite c t1 t2) t3) → (ite c t1 t3)`), shared-else/then hoisting into
  `or`/`and` across two adjacent ites, and (behind an `m_elim_ite` flag) full
  Boolean-ITE-to-and/or elimination.
- `mk_not_core` pushes NOT through an already-negated term, constants, and
  Boolean equality (`(not (= a b))` with `b:Bool` → `(= (not a) b)`)
  (`bool_rewriter.cpp:1113-1131`).
- `poly_rewriter` (`references/z3/src/ast/rewriter/poly_rewriter.h`) is the
  shared AC-polynomial base for `arith_rewriter`/`bv_rewriter`: monomial
  collection, GCD-based cancellation across an equation
  (`cancel_monomials`), and `hoist_ite` — the ITE-through-arithmetic lift
  named in finding §0.6.

**der.cpp** (Destructive Equality Resolution, `references/z3/src/ast/rewriter/der.cpp`)
eliminates a bound variable *inside a quantifier body* when the body contains
a defining (dis)equality `x = t` / `not(x = t)` — `is_var_diseq`
(`der.cpp:44-`). This is DER's scope: **under** a `forall`/`exists`, before
instantiation, as opposed to our `solve_eqs` which orients top-level
assertion equalities. Different scope, same substitute-and-drop principle.

**dom_simplifier.cpp** (`references/z3/src/ast/rewriter/dom_simplifier.cpp`)
computes a dominator tree over the shared expression DAG (`compute_post_order`,
`dom_simplifier.cpp:26-`) so a subterm can be simplified using the truth value
forced by a *dominating* Boolean ancestor (e.g. a subterm known-true because it
is itself an `and`-conjunct dominating its own occurrence elsewhere). This is
genuinely more expensive (a dominator computation over the DAG) and is the
kind of contextual/polarity-aware rewrite we have **none of** — `rewrite_bool_not`
tracks negation *parity* for alpha-equivalence checking only
(`crates/axeyum-rewrite/src/alpha.rs:16-24`), not for propagating a sibling's
known truth value into a rewrite decision.

### cvc5 (`src/theory/rewriter.cpp` + `src/rewriter/` RARE)

**Two-tier structure, confirmed.** `Rewriter::rewriteTo`
(`references/cvc5/src/theory/rewriter.cpp:109,207-`) runs a stack-based
worklist (a `deque<RewriteStackElement>` explicitly chosen over `vector`
"since RewriteStackElement contains a live NodeBuilder... pushing deep stacks
will not relocate existing frames" — comment at `rewriter.cpp:236-237`), with
a **two-phase per-node protocol**: `preRewrite` is looped to its own local
fixpoint (`rewriter.cpp:272-` — `for(;;) { ... }` until
`response.d_status == REWRITE_DONE` and the node's `Kind` stopped changing),
then children are rewritten, then `postRewrite` runs once with status
`REWRITE_AGAIN`/`REWRITE_AGAIN_FULL`/`REWRITE_DONE` deciding whether to loop
again (`rewriter.cpp:372-465`). Each of `preRewrite`/`postRewrite` dispatches
by `theory::TheoryId` to a hand-written C++ `TheoryRewriter`
(`theory_bool_rewriter.cpp`, `arith_rewriter.cpp`, `strings_rewriter.cpp`,
...) — **this hand-written tier is the hot path**, analogous to Z3's
`mk_*_core` tier `[I]`.

**Caching**: `getPreRewriteCache`/`getPostRewriteCache`
(`rewriter.cpp:246,320`) keyed per-`(theoryId, node)`.

**Cost control**: every iteration of the rewrite loop spends one resource
unit — `d_resourceManager->spendResource(Resource::RewriteStep)`
(`rewriter.cpp:248`) — against cvc5's global resource/time budget, so a
pathological rewrite loop is caught by the same mechanism that limits solver
search, not a rewriter-local counter. `[C]`

**RARE, the declarative rule DSL** (`references/cvc5/src/theory/*/rewrites`,
e.g. `builtin/rewrites` 12 lines, `booleans/rewrites` 76 lines,
`arith/rewrites` 141 lines, `strings/rewrites` 745 lines). Verbatim syntax
`[C]` (`references/cvc5/src/theory/builtin/rewrites`,
`references/cvc5/src/theory/booleans/rewrites:1-76`):

```lisp
(define-rule ite-true-cond ((x ?) (y ?)) (ite true x y) x)
(define-rule ite-not-cond ((c Bool) (x ?) (y ?)) (ite (not c) x y) (ite c y x))
(define-cond-rule bool-not-true ((t Bool)) (= t false) (not t) true)   ; guarded
(define-rule bool-and-conf
  ((xs Bool :list) (w Bool) (ys Bool :list) (zs Bool :list))
  (and xs w ys (not w) zs) false)                                      ; :list = variadic AC slice
(define-rule* bool-or-de-morgan ((x Bool) (y Bool) (zs Bool :list))    ; define-rule* = recursive/fixpoint rule
  (not (or x y zs)) (not (or y zs)) (and (not x) _))                   ; `_` = "recurse here"
```
Four rule forms: `define-rule` (unconditional pattern→replacement),
`define-cond-rule` (a side condition that must itself reduce to `true`),
`define-rule*` (a self-recursive rule that peels one element off a `:list`
slice at a time, `_` standing for "apply this same rule again to the
smaller instance" — this is how a rule handles arbitrary-arity AND/OR without
a hand-written loop), and typed bindings (`(x Bool)`, `(x ?)` = any sort).
This is the concrete shape of "a rule set that is data": these files are read
and compiled by `mkrewrites.py`/`mkrewriter.py`
(`references/cvc5/src/rewriter/mkrewrites.py`,
`references/cvc5/src/theory/mkrewriter.py`) into the `RewriteDb`
(`references/cvc5/src/rewriter/rewrite_db.cpp/.h`) that both a runtime
matcher and the proof reconstructor consume — **one rule definition, two
consumers**, which is exactly what our manifest does not yet give us (finding
§0.1).

**Relationship between the two tiers**: RARE-declared rules are *not* the hot
rewrite path by default — hand-written `TheoryRewriter::preRewrite`/
`postRewrite` C++ remains the primary dispatch (confirmed by
`Rewriter::preRewrite`/`postRewrite` calling `d_theoryRewriters[theoryId]`
directly, `rewriter.cpp:513-540`); RARE's `RewriteDb` is consulted
specifically during **proof reconstruction** (`RewriteDbProofCons`,
`references/cvc5/src/rewriter/rewrite_db_proof_cons.h`) and by the extended/
candidate rewriter used for rewrite-rule *discovery*
(`references/cvc5/src/theory/quantifiers/extended_rewrite.cpp`,
`candidate_rewrite_database.cpp`) — not proven to be the live default rewrite
path itself; I did not trace far enough to confirm RARE rules also fire
during ordinary `rewrite()` calls versus being reconstruction-only. Flagging
as **not fully verified** rather than asserting either way.

**Proof reconstruction is lazy/on-demand, not eager-per-step.**
`RewriteDbProofCons` — cited directly in its own header comment as
implementing "Reconstructing Fine-Grained Proofs of Rewrites Using a
Domain-Specific Language", Noetzli et al., **FMCAD 2022**
(`references/cvc5/src/rewriter/rewrite_db_proof_cons.h:36-38`) — and
`basic_rewrite_rcons.h`, whose header comment names it "the module for basic
(non-DSL-dependent) automatic reconstructing proofs of THEORY_REWRITE steps"
(`references/cvc5/src/rewriter/basic_rewrite_rcons.h:11-12`). Both are
separate modules invoked only when a full proof is requested — the ordinary
`Rewriter::rewrite()` path does not build a proof object at all unless
`Rewriter::rewriteWithProof`/`d_tpg` (`TConvProofGenerator`,
`rewriter.cpp:141-153`) is engaged. This is the answer to the task's §5
question directly: **cvc5 keeps rewriting cheap by not touching the proof
machinery on the fast path, and reconstructs a proof after the fact by
re-deriving which rule justifies each observed before/after pair**, using the
same rule database the fast rewriter's hand-written C++ mirrors. `[C]`

**Preprocessing-level rewrite passes beyond the core theory rewriter**:
`references/cvc5/src/preprocessing/passes/rewrite.cpp` (a pass that just
calls the core rewriter over the whole assertion set once, at pipeline
scope), `static_rewrite.cpp` (rewrites usable before all preprocessing
passes have run, i.e. an early cheap subset), and `learned_rewrite.cpp`
(rewrites informed by facts *learned* elsewhere in preprocessing/solving —
e.g. a variable proven bounded gets its range substituted in). I read the
file names/headers but did not trace `learned_rewrite.cpp`'s internals in
depth; flagging as a pointer for follow-up, not a fully verified claim.

## 2. E-graphs and equality saturation

**egg (egraphs-good/egg), POPL 2021** `[P]`/`[W]` (arxiv 2004.03082,
`https://www.mwillsey.com/papers/egg`):

- **E-node/e-class model.** An e-node is an operator applied to a list of
  child *e-class ids* (not e-node ids) — this indirection through e-classes
  is exactly what lets one e-class represent an equivalence set. An
  `EClass` groups e-nodes known equal; a union-find (`Id`) tracks class
  membership. `[W]` (docs.rs/egg).
- **Hashcons + why it goes stale.** The e-graph maintains a hashcons
  (canonical e-node → e-class id) so structurally identical e-nodes share a
  class — same idea as our `TermArena` interner
  (`crates/axeyum-ir/src/arena.rs:44`). But after a `union(a, b)`, e-nodes
  that mention `a` or `b` as children may now be congruent to other e-nodes
  that were not congruent before the union — the hashcons and congruence
  invariants go stale until re-checked.
- **Rebuilding.** egg's core contribution: instead of restoring the
  hashcons/congruence invariant inside every `union` call (eager, as our
  `axeyum-egraph::EGraph::merge` does — confirmed eager: `merge` calls
  `process_pending()` synchronously, `crates/axeyum-egraph/src/lib.rs:987-994`),
  egg **defers** it: `union` only records which e-classes need "upward
  merging" on a worklist; a separate `rebuild()` call, invoked once per
  equality-saturation iteration (not per union), processes that worklist and
  restores both invariants together. This amortizes what would otherwise be
  O(unions × parents) eager congruence propagation into one batched pass per
  iteration. `[P]` (search result summary of the POPL 2021 paper's abstract
  and rebuilding section).
- **`Analysis` trait**: attaches arbitrary data to each e-class (e.g. a
  constant value, if known) with a `merge` function combining two classes'
  analysis data on union — this is how constant folding happens *inside*
  saturation without a separate pass. `[W]`
- **Extraction**: after saturating (running the rule set to a fixpoint or a
  size/time/iteration limit), pull one concrete term back out via a
  `CostFunction` (`AstSize`, `AstDepth`, or an ILP-based `LpExtractor`) and a
  bottom-up dynamic program over the e-graph. `[W]`
- **Rewrite application**: a `Rewrite` = `Searcher` (pattern match, producing
  substitutions) + `Applier` (build the replacement); *all* rules in the set
  are searched and applied together each iteration before extracting — this
  is what "equality saturation" means as opposed to committing to one
  rewrite (and hence one term shape) at a time, which sidesteps the classic
  compiler "phase-ordering problem" of sequential rewrite passes. `[W]`

**Where saturation is NOT worth it — the AC blowup, confirmed across
multiple sources** `[W]` (arxiv 2504.11574 "E-morphic", arxiv 2507.11897
"Towards Relational Contextual Equality Saturation", and others found via
search): "a long chain of multiplication can be rewritten to an exponential
number of permutations under associativity and commutativity (AC rules)" —
this is precisely the failure mode our `AC_REBUILD_MAX_OPERANDS` cap and Z3's
committed-canonical-form approach both sidestep by *never* representing more
than one canonical shape per AC operand multiset. As e-graphs grow,
"iterations become slower and require more memory," and for many rule sets
"e-classes tend to run away" as the fraction of e-nodes on a cost-minimal
extraction path shrinks. Mitigations in the literature (relational
e-matching — reduces matching to worst-case-optimal conjunctive query
answering, arxiv 2108.02290; sampling a bounded number of matches per rule
per iteration) are active research, not settled production practice. **No
evidence found of a production SMT solver (Z3, cvc5, Bitwuzla, ...) using
full equality saturation as its primary term-simplification stage** — both
Z3 and cvc5 rewrite to a syntactic (single-form) fixpoint, as described in
§1, not saturation. This absence-of-evidence is itself informative for the
"is it worth it" question and is my synthesis (`[I]`), not a sourced
negative claim.

**E-matching for quantifiers is a different, older, narrower technique** —
de Moura & Bjørner, "Efficient E-matching for SMT Solvers," CADE 2007 `[P]`
(confirmed via search and via cvc5's own header comment naming a *different*
2022 paper for proof reconstruction, so these are not the same work). Key
idea: **incremental** matching of a *trigger* pattern against a **live**
congruence-closure e-graph the solver's core already maintains, invoked when
new equalities arrive (not a batch saturate-then-extract pass); Z3's
implementation uses "E-matching code trees" (combining substitution trees
and code trees, matching several patterns simultaneously) plus an "inverted
path index" that filters which e-graph terms might newly match a pattern
when the graph is updated. `[W]`. **Our counterpart exists and is exactly
this older technique, not equality saturation**: `axeyum-egraph::EGraph`
is a backtrackable (`push`/`pop`) congruence-closure e-graph with **eager**
merge/rebuild (unlike egg), used by `instantiate_with_triggers`
(`crates/axeyum-rewrite/src/quantifiers.rs:472-641`) via `EMatchIndex`/
`ematch_many_indexed` (`crates/axeyum-egraph/src/lib.rs:166-656`) for
trigger-based universal instantiation, and separately by
`crates/axeyum-solver/src/euf_interpolant.rs` and `euf_alethe.rs` for EUF
congruence-closure reasoning and Alethe proof emission from e-graph
`explain_steps`. **This e-graph is not used by `axeyum-rewrite` for general
term simplification** — confirmed by `crates/axeyum-rewrite/Cargo.toml`,
whose only dependency is `axeyum-ir` (`Cargo.toml:14-15`). The e-matching
frontier growth cap in `axeyum-egraph`
(`crates/axeyum-egraph/src/lib.rs:34-105`, citing a measured 15.8 GB/150 s
blowup on one benchmark) is documented evidence of exactly the same
combinatorial-matching cost the equality-saturation literature warns about
(§2 above), independently discovered here.

## 3. High-value general rewrites — what exists, concretely

All rule IDs below are read from `crates/axeyum-rewrite/src/canonical.rs:63-108`
(the manifest constant table) and their firing logic in the functions named.

| Rewrite class | Present in ours | Where | Notes |
|---|---|---|---|
| Constant folding (bool/bv/int) | Yes | `bool.const_fold.v1`, `bv.const_fold.v1`, `int.const_fold.v1` (`fold_ground_int`, `canonical.rs:2919-`) | Gated on `all_constant` |
| AC operand ordering for sharing | Yes | `commutative.operand_order.v1`, `flatten_ac`/`rebuild_balanced` (`canonical.rs:1598-1746`) | Sort-by-`TermId` + balanced rebuild, capped at 64 operands (measured, see §0.8) |
| ITE lifting/collapsing | Partial | `ite.const_condition.v1`, `ite.same_branches.v1`, `ite.bool_identity.v1` (`rewrite_ite`, `canonical.rs:2369-2422`) | No ITE-through-arithmetic hoist (§0.6), no nested-condition/shared-branch hoisting across sibling ites (Z3 has both) |
| Boolean structure simpl. | Partial | `bool.double_not.v1`, and/or identity/annihilator/idempotent, xor identity/self, implies rules (`canonical.rs:1748-1952`) | No n-ary complementary/duplicate-literal short-circuit (§0.5) |
| Unconstrained-variable elim | Yes | `crates/axeyum-rewrite/src/elim_unconstrained.rs` | Invertible-op peeling (bvadd/bvsub/bvxor/bvnot/odd-bvmul), model-sound via reconstruction trail |
| Equality orientation + substitution (solve-eqs) | Yes | `crates/axeyum-rewrite/src/solve_eqs.rs` | Top-level only; no DER-style under-quantifier elimination (§0.7) |
| Pure-literal / skeleton reasoning | Partial | `propagate_values.rs` (top-level literal facts only) | No n-ary AND/OR contradiction short-circuit (§0.5); no general pure-literal-over-Boolean-skeleton pass |
| Array read-over-write | Yes | `crates/axeyum-rewrite/src/arrays.rs` (`eliminate_arrays`, `abstract_arrays`) | Also does Ackermann reduction, index-width-capped extensionality |
| UF Ackermannization | Yes | `crates/axeyum-rewrite/src/functions.rs` | Same shape as arrays |
| Datatype read-over-construct | Yes | `crates/axeyum-rewrite/src/datatypes.rs` | `select_i(construct_c(...))`, `is_c(construct_d(...))` |
| Integer div/mod-by-constant elimination | Yes | `crates/axeyum-rewrite/src/int_divmod.rs` | Correctly handles the constant-zero underspecified case as a fresh variable (explicit callback to the `a946f925` regression, `int_divmod.rs:11-18`) |
| Alpha-equivalence / quantifier-negation duality | Yes | `crates/axeyum-rewrite/src/alpha.rs` | Used as an independent checker, not just a rewrite |
| Trigger-based/enumerative quantifier instantiation | Yes | `crates/axeyum-rewrite/src/quantifiers.rs` | E-matching via `axeyum-egraph` |
| n-ary Boolean skeleton short-circuit | **No** | — | Z3 has it (§1, `mk_nflat_and_core`) |
| ITE-through-non-Boolean-op hoist | **No** | — | Z3 has it (`poly_rewriter::hoist_ite`) |
| Dominator/polarity-context-aware simplification | **No** | — | Z3 has it (`dom_simplifier.cpp`) |
| DER (equality elim under a quantifier body) | **No** | — | Z3 has it (`der.cpp`); our `solve_eqs` is top-level only |

## 4. Cost model

**Always-on / cheap, in both Z3 and ours**: constant folding, single-step
identity/annihilator rules, AC flatten+sort (bounded). **Gated / expensive**:
Z3's `dom_simplifier` (dominator computation over the whole DAG) and
`maximize_ac_sharing` (a global side cache) are optional passes, not part of
the default `mk_simplified_app` always-on tier — confirmed by their being
separate classes invoked by specific tactics, not by `mk_core`'s dispatch
table (`mk_simplified_app.cpp:44-77` names only bool/arith/bv/array/datatype/
fpa rewriters, not `dom_simplifier` or `maximize_ac_sharing`). Ours has no
"expensive, opt-in" tier at all in `axeyum-rewrite` — every module exported
from `lib.rs` runs whenever its caller invokes it; gating is per-pass (call
`eliminate_arrays` or don't) rather than per-rule-inside-a-pass; `[I]` this
is consistent with the repo's stated preference for a fixed pipeline of
individually-bounded passes over one configurable recursive rewriter.

**Avoiding quadratic blowup on large shared DAGs**: both systems rely on the
same two mechanisms — (a) hash-consing/interning so a DAG node is visited
once regardless of fan-in (Z3's `ast_manager`, our `TermArena`
(`crates/axeyum-ir/src/arena.rs:44`)), and (b) a rewrite-result cache keyed
by the *pre-rewrite* node so a shared subterm's rewrite is computed once
(Z3's `must_cache`-gated `act_cache`; cvc5's `getPreRewriteCache`/
`getPostRewriteCache`; our `memo: HashMap<TermId, TermId>` shared across all
roots in one `canonicalize_terms` call, `canonical.rs:1176,1233`). The
`solve_eqs` doc comment states this explicitly for our substitution pass:
"terms are DAG-interned, so substituting `x := t` shares `t`'s nodes rather
than copying them" (`solve_eqs.rs:20-22`).

**Maximal structural sharing**: `TermArena`'s hash-consing is the substrate
every other cost-control mechanism in this crate depends on — verified by
its doc comment: "structurally equal terms intern to the same `TermId`"
(`crates/axeyum-ir/src/arena.rs:10-12`).

## 5. Proof obligations

Covered in detail in §1's cvc5 subsection. Summary of the two working models
found in production solvers, for direct comparison against our current gap
(§0.2):

- **Z3: eager, inline, optional.** A `proof_ref` is threaded through
  `rewriter_tpl` alongside the rewritten term whenever `m_proof_gen` is set;
  each step builds a `mk_rewrite`/`mk_congruence`/`mk_transitivity` proof
  object as the term is rewritten (`rewriter_def.h:296-419`). Cost: proof
  generation is a compile-/run-time-toggleable mode, not a separate pass —
  when off, none of this machinery runs.
- **cvc5: lazy, reconstructed on demand, keyed off a rule database.** The
  fast `rewrite()` path never touches proof machinery
  (`theory/rewriter.cpp`'s `rewriteTo` has no proof parameter in its default
  call chain). A full proof, if requested, is reconstructed afterward by
  `RewriteDbProofCons`/`basic_rewrite_rcons`, which re-derives which RARE
  rule (or which hand-written theory rewrite, via `TheoryRewriteMode`
  `STANDARD`/`RESORT`/`NEVER`, `basic_rewrite_rcons.h:36-42`) justifies each
  observed before/after node pair, citing Noetzli et al. FMCAD 2022 by name
  in its own source comment.

Given ADR-0601/0602/0603's requirement that CAS/producer evidence either
reconstructs into the trusted kernel or is visibly `cas-internal`, the cvc5
shape (reconstruct-on-demand from a named rule, rather than log every
micro-step eagerly) is the one that keeps the hot rewrite path cheap while
still making every commit *justifiable after the fact* — and it is directly
buildable on what we already have: every `RewriteRule` already carries a
stable `RewriteRuleId` (`crates/axeyum-rewrite/src/lib.rs:80-101`) and
`RewriteReport::record` already logs `(rule_id, before, after)` for every
committed application (`canonical.rs:246-296`, consumed by
`PreconditionCheck`/`RewriteReport` — I did not check whether this trail is
currently surfaced to any caller outside the crate; flagging as unverified).
What is missing is a checker that can take one `(rule_id, before, after)`
triple from that trail and independently re-derive *why* it's sound —
today only the runtime `PreconditionCheck` samples denotational equivalence
inline (§0.3); nothing replays it after the fact from a rule database the
way cvc5's reconstructor does.

## 6. What axeyum-rewrite already has — architecture summary

- **Manifest = metadata, not logic.** `RewriteManifest`/`RewriteRule`
  (`lib.rs:220-320`) is a checked table of IDs, preconditions (a
  `PreconditionGuard` — either `AnyOperator` or an enumerated
  `RootOperators` list, checked by operator *discriminant* only, never by
  operand shape), preservation class (`Denotation` vs `Equisatisfiable`),
  model-projection obligation, required test routes, and a default-enabled
  flag. `RewriteManifest::new` enforces real invariants: no duplicate IDs, no
  empty operator scope, every default-enabled equisatisfiable rule must have
  an *implemented* (not just *required*) projection and a
  `ModelProjectionReplay` test (`validate_projection`,
  `lib.rs:305-346`) — this is a genuinely load-bearing contract layer, not
  decoration.
- **The transform itself lives in `canonical.rs`'s `rewrite_app`**, a single
  ~1200-line match over `Op` that calls one `rewrite_*` function per operator
  family (`canonical.rs:1335-2707`), each function individually checking
  `enabled.contains(RULE_ID)` before firing. This is where finding §0.1's gap
  lives: the manifest cannot regenerate this logic; it can only forbid an
  operator from being default-enabled if its metadata contract isn't met.
- **Fixpoint shape**: one bottom-up post-order pass per call to
  `canonicalize_terms` (shared memo across all roots), with a *local*
  bounded re-offering loop at each rewritten node
  (`DEFAULT_LOCAL_REWRITE_FUEL = 8`) — no whole-DAG outer fixpoint loop.
  Verified: `canonicalize`/`canonicalize_terms` (`canonical.rs:513-546`) call
  `canonicalize_root` exactly once per root; nothing re-invokes the
  canonicalizer over its own output. `[I]` a caller wanting a full fixpoint
  across passes (e.g. after `solve_eqs` exposes a new constant-foldable
  term) must currently sequence multiple pass calls explicitly — the
  pipeline is "run each bounded pass once, in a fixed order," not "loop the
  whole pipeline to convergence."
- **Runtime soundness guard unique to this codebase**: `PreconditionCheck`'s
  two-tier check (structural operator/sort scope, always on; denotational
  sampling over up to `DENOTATION_GUARD_SAMPLES` fixed assignments,
  policy-gated) refuses to commit any rewrite whose sampled before/after
  values disagree, with a dedicated `#[cfg(test)]`-only *wrong* rewrite
  (`control_rewrite`, `canonical.rs:1276-1326`) proving the guard is wired
  into the commit path, not just unit-tested in isolation. No equivalent
  exists in Z3 or cvc5's *production* rewriter (their soundness assurance for
  built-in rewrites is offline testing/fuzzing, not an inline runtime
  sampler) — this is a place we are ahead, not behind.
- **Model-sound elimination passes share one reconstruction primitive**:
  `ModelReconstructionTrail` (`reconstruct.rs`) is used identically by
  `propagate_values`, `solve_eqs`, and `elim_unconstrained` — append
  `Define{sym, definition}` in elimination order, replay in reverse. This is
  exactly the "separable decision" the task asked to name: *elimination
  passes* and *model reconstruction* are already factored apart from each
  other and reusable independently of the canonicalizer.
- **`axeyum-egraph` is a separate, already-built e-graph** (congruence
  closure + backtracking + e-matching + proof-forest `explain`), consumed by
  quantifier instantiation and by EUF/interpolant code in `axeyum-solver`,
  but **not wired into `axeyum-rewrite` at all**. Its `merge` is eager
  (processes the congruence-closure worklist synchronously,
  `crates/axeyum-egraph/src/lib.rs:987-994`), unlike egg's deferred
  rebuilding — a reasonable choice for its actual job (live congruence
  closure driven incrementally by a solver core) but not the batch-saturate-
  then-extract shape equality saturation needs if anyone later wanted to
  build a saturation-based subterm optimizer on top of it.

## Absences checked and confirmed genuine (not false negatives)

Each of the following was checked by reading the relevant module's full rule
list / dispatch table, not by grepping for a name:

- No declarative pattern→replacement rule table anywhere in
  `axeyum-rewrite` (every transform is a Rust function).
- No rewrite-step proof or certificate emission in `canonical.rs` or any
  sibling module in the crate.
- No n-ary Boolean contradiction/tautology/duplicate-literal short-circuit
  during AND/OR flattening (`flatten_ac_bounded` sorts and preserves
  multiplicity only; the only complementary-pair rule is the binary
  `bool.and_annihilator.v1`/`bool.or_annihilator.v1`, not an n-ary scan).
- No ITE-hoisting-through-arithmetic/bit-vector-operator rule.
- No dominator- or polarity-context-aware simplification.
- No DER-style equality elimination *inside* a quantifier body (our
  `solve_eqs` is assertion-top-level only; `quantifiers.rs` does
  instantiation, not intra-body variable elimination).
- `axeyum-rewrite` has zero dependency on `axeyum-egraph` (checked
  `Cargo.toml`), so no part of the canonicalizer uses e-matching or
  congruence closure; those exist only in the quantifier-instantiation and
  solver-internal (EUF/interpolant) code paths.

## Not verified / out of scope for this pass

- Whether RARE-declared rules fire on cvc5's *default* live `rewrite()` path
  versus being consulted only by the proof reconstructor and the
  extended/candidate-rewrite quantifier machinery (§1, flagged explicitly).
- The internals of `references/cvc5/src/preprocessing/passes/learned_rewrite.cpp`
  beyond its stated purpose.
- Whether `RewriteReport`'s `(rule_id, before, after)` trail
  (`canonical.rs:246-296`) is surfaced to any external caller today, or is
  purely internal audit state.
- Z3's `bv_bounds_base.h` (interval/bounds-propagation rewriting) — located
  but not read in this pass; a plausible next-lane target given our own
  lack of any range/bounds-driven rewrite.
