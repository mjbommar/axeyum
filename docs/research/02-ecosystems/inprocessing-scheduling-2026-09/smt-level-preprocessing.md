# SMT-level (word-level) preprocessing: what frontier BV solvers do before bit-blasting

**Lane:** `research-smt-preproc` (read-only research lane, 2026-09-08)
**Sibling file in this directory:** `cadical-kissat-budget-model.md` (SAT-side budget model, different lane).

**Claim tags used throughout.** `[C]` = read in solver source, with `file:line`.
`[P]` = from a paper or system description. `[I]` = my inference, not verified.
Where I did not verify something, the text says **did not verify** rather than
guessing.

**Source trees read.** Shallow clones in the gitignored `references/`:

- `references/bitwuzla` — `bitwuzla/bitwuzla` @ `a5e6e8a7ad511975c495455924d0868bcdc304ea` (2026-09-04)
- `references/z3` — `Z3Prover/z3` @ `e18d63bda04fcab8240eb55314d567db3e43d540` (2026-09-08)
- `references/cvc5` — already present on this host; used only for the two
  spot-checks named in §7.

The first two were cloned by this lane with `git clone --depth 1`;
`scripts/fetch-references.sh` already lists all three, the first two were simply
not present on this host. **Other hosts may lack them** — re-run that script
before re-verifying anything here.

**How this was produced, so the next lane can weigh it.** The Bitwuzla source
(§1), the repository inventory (§4), the architecture (§5) and the corpus
measurement (§6) are my own reads. §2 (Z3) and §7 (literature) were produced by
two parallel research lanes; I re-verified their load-bearing claims directly
before folding them in — the QF_BV preamble ordering, the dead
`collect_num_occs`, the `else if (false && …)` in `bv_bounds_base.h`, cvc5's
`bv-gauss` default, and cvc5's `unconstrainedSimp` incremental gating all check
out exactly as reported.

All `file:line` citations below are relative to those two directories unless the
path starts with `crates/`, which means this repository.

---

## Summary

**The finding that reframes the brief.** I was asked what we are leaving on the
table at the word level. The answer is real but smaller and less certain than the
pass lists suggest: **nobody has published a pass-level ablation for a modern
bit-vector preprocessor.** The Bitwuzla CAV 2023 paper has none; **zero** of ~20
BV-relevant SMT-COMP system descriptions 2022–2025 contains one; there is no
SMT-COMP competition report at all for those years. Where ablations do exist,
two of the best-known BV preprocessing techniques measured **negative in their
own authors' evaluations** — slicing as a decision procedure, and AIG rewriting
before CNF. And the two largest measured numbers in this whole space are **not
word-level at all**: CNF-level blocked-clause and bounded-variable elimination.
Details and citations in §7.

That does not mean the layer is worthless — it means **the instrumentation is
the first deliverable, not an afterthought.**

Six things worth acting on:

1. **We have nine word-level passes and no pass framework.** The pipeline is
   hard-coded twice, with *different* semantics (8 fixpoint rounds in
   `preprocess.rs`, a single round in `auto.rs`), and there is nowhere to add a
   tenth. Building it with per-pass statistics would give us **the pass-level
   ablation the field does not have**, on our own corpora, in one bench run.
   §1.2, §5, §8.1.
2. **Our `solve_eqs` handles one of the five solved forms Bitwuzla's
   `variable_substitution` handles** — missing Gaussian elimination over Z/2^w,
   concat splitting, inequality-derived width reduction, and variable slicing.
   Z3 implements the same Gaussian rules independently. §1.5, §2.7, §3.3.
3. **`elim_unconstrained` covers six operators; Z3's covers most of the
   language**, including all of arithmetic — which fires in five divisions where
   we currently have no word-level reduction of this kind. **This is the
   best-evidenced item in the document**: measured across three unmodified
   solvers at +8/+314 (Boolector) and +2/+195 (Z3) for 0.03 s average cost.
   Ours also recomputes occurrence counts over the whole forest after *every
   single* elimination — the exact inefficiency Z3 rewrote its version to fix.
   §2.2, §4.1, §7.2.
4. **There is no shared BV inverter.** Both Z3 and Bitwuzla factored inversion
   into a separate component with three consumers each — Z3's is a per-theory
   plugin registry with an injected "is unconstrained?" predicate. Ours is a
   private six-operator function. §5.2b.
5. **Two cheap cross-division wins the brief did not ask about.** Gating
   Ackermannization on a linear-time count (**+132 solved, ~3× less time**), and
   input normalization (**<0.8% overhead for an order-of-magnitude reduction in
   run-to-run variance** — directly relevant to our "determinism is a public API
   promise" rule). §7.2, §8.2.
6. **We already have more than I expected, and I had to withdraw one claim.**
   Our AIG→CNF encoder is ahead of Bitwuzla's on four counts; we already gate the
   whole preprocessing reduction on lowered AIG size; and four items I was ready
   to propose are already documented and ranked in a sibling survey. §0.1, §4.

The full ranking, with effort estimates, evidence, and which items are new, is §8.

---

## 0. Why this layer, in one paragraph

Bit-blasting is a lossy compiler. Once `(bvmul a b)` becomes 4096 AND gates, no
CNF-level technique recovers the fact that it was a multiplier, that `a`'s top 24
bits were provably zero, or that `b` occurred exactly once. Every frontier BV
solver therefore runs a **word-level preprocessing pipeline to fixpoint before
the bit-blaster is ever called**, and the passes there are cheap precisely
because the term DAG is small (thousands of nodes) compared to the CNF
(millions of literals). Bitwuzla's whole preprocessing subsystem is 6,699 lines
`[C: src/preprocess/**]` against a 13,221-line rewriter `[C: src/rewrite/*]` —
tiny next to its SAT dependency, and it is where its QF_BV lead is built.

## 0.1 Relationship to the surveys already in `docs/research/02-ecosystems/`

**Read this before acting on §8.** Two sibling documents already cover parts of
this ground, with the same references and often the same line citations. I found
them *after* drafting, which is itself the finding: re-derivation is the default
failure mode here.

Already covered — **do not re-propose, cite instead**:

| Topic | Where it already lives |
|---|---|
| The complete Brummayer–Biere two-level AIG rule set, transcribed | `pipeline-survey-2026-09/bitblasting-and-aig.md` §2.2, and ranked as its **Rank 4** |
| Fanout counts on `Aig` as the prerequisite for the above | same file, **Rank 3** |
| Our AIG→CNF encoder being ahead of Bitwuzla's (n-ary AND, native XOR, Plaisted–Greenbaum) | same file, §2.6 — its conclusion is "there is no Bitwuzla feature here to port" |
| `elim_udiv` (define-and-assert div/rem), with the full side-condition set | same file, §2.7 |
| Skeleton preprocessing (SAT-simplify the Boolean abstraction, harvest fixed literals) | same file, §2.8 |
| `AigScore` and its interleaved-budgeted-race shape | same file, §1.5 |
| CNF-level blocked clause elimination, with a QF_BV-specific size measurement | same file, **Rank 2b** |
| Measuring the AIG-rewriting ceiling with ABC before building any of it | same file, **Rank 0** |
| Our existing rule manifest, and the "rules should be data not match arms" argument | `pipeline-survey-2026-09/term-rewriting-infrastructure.md` §0 items 1-2 |
| Z3's **rewriter** (`src/ast/rewriter/`), its caching, and the ITE-hoist / dominator-simplifier / DER gaps | same file, §1 and §3 |

Note the boundary on that last row: the existing survey covers Z3's
`src/ast/rewriter/`. It does **not** cover `src/ast/simplifiers/` — the pass
framework — nor `elim_unconstrained.cpp`, `bv_slice.cpp`, `max_bv_sharing.cpp`,
or `bv_size_reduction_tactic.cpp`. Verified: `grep -rn "ast/simplifiers|bv_slice|
max_bv_sharing|bv_size_reduction|elim_uncnstr|dependent_expr|then_simplifier|
extract_eqs" docs/` returns nothing outside this file. §2 below is therefore new
ground.

**And one claim I had to withdraw.** I initially recorded "no AIG cost oracle
anywhere in the tree". That is false: `reduction_shrinks_encoding`
(`crates/axeyum-solver/src/auto.rs:1975-2010`) already accepts or rejects the
*whole* preprocessing reduction by lowering both the original and the reduced
query and comparing AIG node counts, with three measured benchmarks in its doc
comment — including `062-bench_2195`, whose term DAG **shrank** 1375 → 1215
while its AIG **grew** 35 329 → 51 724. The sibling survey had already recorded
this. See §4.2 for the corrected statement of what is actually missing.

What is **not** covered anywhere in `docs/`, verified by searching for
`variable_substitution`, `gaussian`, `slicing`, `non-overlap`,
`embedded_constraint`, `flatten_and`, `EXTRACT_ADD_MUL`, `BvInverter` across
`docs/research/02-ecosystems/**`:

- Bitwuzla's `variable_substitution` pass and **all five** of its sub-rules
  (§1.5): Gaussian elimination over Z/2^w, concat splitting of equalities,
  inequality-derived width reduction, extract elimination / variable slicing,
  and the two-stage cycle removal.
- `flatten_and` and `embedded_constraints` (§1.4, §1.7).
- `BV_EXTRACT_ADD_MUL` — pushing an extract through a whole add/mul sub-DAG (§3.1).
- The factoring rule family `NORM_FACT_BV_*` (§3.2).
- The shared `BvInverter` and its three consumers, including BV-generalized
  destructive equality resolution for quantifiers (§5.2b).
- The preprocessing **pass framework** itself: pass trait, assertion vector,
  driver, per-pass budgets and statistics (§1.1, §1.2, §5).
- The cached structural bitset on interned nodes (§5.6).

That list is what §8 ranks. The already-covered items appear in §8 only as
cross-references.

---

---

## 1. Bitwuzla: the pass list, in execution order

### 1.1 The driver

`Preprocessor::apply` `[C: src/preprocess/preprocessor.cpp:236-401]` is a
**do/while fixpoint over the whole pass list**, per assertion scope level:

```
repeat {
  modified = false
  rewrite                                   (always on)
  flatten_and                 if pp_flatten_and
  variable_substitution       if pp_variable_subst   -- INNER fixpoint loop
  skeleton_preproc            if pp_skeleton_preproc AND not yet done   (once only)
  embedded_constraints        if pp_embedded_constr
  elim_lambda                               (always on)
  elim_udiv                   DISABLED in source (`if (false && ...)`)
  normalize                   if pp_normalize AND rewrite_level>=2 AND first check-sat
  quant                       if pp_quant
} until (!modified || inconsistent || terminate)
```

Details that matter for a reimplementation `[C]`:

- Each pass is called as `assertions.reset_modified(); pass.apply(assertions);
  modified |= assertions.modified();`. The **modified flag lives on the assertion
  vector, not on the pass** — a pass signals progress by mutating the vector,
  never by returning a bool (`preprocessor.cpp:271-273`).
- `variable_substitution` gets its **own inner `do…while(assertions.modified())`
  loop** (`preprocessor.cpp:300-309`) — it is the one pass run to its own
  fixpoint before control returns to the outer loop. That is a statement about
  its value.
- Two passes are **budget-gated, not correctness-gated**:
  `skel_done = !assertions.initial_assertions()` — skeleton preprocessing runs
  **once, on the initial assertion set only**, "to limit the overhead"
  (`preprocessor.cpp:257-259`); and `apply_normalization = d_num_preprocess == 1`
  — normalization runs **only on the first `check-sat`**, "for incremental it may
  be too expensive" (`preprocessor.cpp:260-261`).
- Early exit on inconsistency is checked after **every** pass, and the whole
  preprocessing result is `UNSAT` if the assertion set became inconsistent
  (`preprocessor.cpp:140-144`).
- There is a second, much shorter entry point, `Preprocessor::process(term)`
  (`preprocessor.cpp:147-158`), used to push a single new term (e.g. a lemma)
  through a **subset** of the passes: `rewrite → variable_substitution →
  elim_lambda → embedded_constraints → rewrite`. Note the sandwich: rewrite at
  both ends.

### 1.2 The pass interface (the abstraction to copy)

`[C: src/preprocess/preprocessing_pass.h:34-122]`

```cpp
class PreprocessingPass {
  virtual void apply(AssertionVector& assertions) = 0;   // the pass
  virtual Node process(const Node& term) { return term; } // single-term form
  void clear_cache();
  const std::string& id() / name();
  const auto& statistics() const;
 protected:
  std::pair<Node,uint64_t> substitute(node, SubstitutionMap, cache) const;  // SHARED
  bool cache_assertion(const Node&);   // "have I already looked at this assertion?"
  bool processed(const Node&);
};
```

What the framework supplies, and every pass reuses:

1. **A shared DAG-substitution routine** with an explicit, caller-owned cache
   (`substitute`). This is the single most-reused primitive.
2. **A per-pass processed-assertion set** (`d_processed_assertions`) so a pass can
   cheaply skip assertions it already examined across fixpoint rounds.
3. **A backtrackable map type** (`backtrack::unordered_map`) so substitutions
   survive `push`/`pop` correctly — every stateful pass takes a
   `backtrack::BacktrackManager*` in its constructor.
4. **Per-pass timers and counters** wired into one statistics registry
   (`Statistics{ TimerStatistic& time_apply; }`).
5. **`AssertionVector`** `[C: src/preprocess/assertion_vector.h:28-96]` — the
   mutable view of one scope's assertions, with `replace(i, node)`,
   `push_back(assertion, parent)`, `modified()`, `num_simplified()`,
   `initial_assertions()`, and `is_inconsistent()`. The `parent` argument on
   `push_back` is what feeds the unsat-core assertion tracker.
6. **A shared rewriter** reachable as `d_env.rewriter()`; almost every pass ends
   its own work with `d_env.rewriter().rewrite(result)`.

### 1.3 `rewrite` — the always-on canonicalizer

`[C: src/preprocess/pass/rewrite.cpp]` (56 lines) is a thin wrapper that maps
`d_env.rewriter().rewrite()` over each assertion. The substance is in
`src/rewrite/`: **296 rewrite rule kinds** `[C: enum RewriteRuleKind,
src/rewrite/rewriter.h:372]`, split across `rewrites_bv.cpp` (4,376 lines),
`rewrites_core.cpp` (1,844), `rewrites_bool.cpp` (723), `rewrites_fp.cpp` (822),
`rewrites_bv_norm.cpp` (428), `rewrites_array.cpp` (56).

Rules are **graded by level** `[C: src/rewrite/rewriter.h:55-70]`:
`LEVEL_MAX = 2` (the default), with `LEVEL_ARITHMETIC = 3` used only by the
normalization pass's private rewriter instance. `rewriter.cpp` is full of
`if (d_level >= 1)` / `if (d_level >= 2)` guards. **Level is the cost knob**: 0 =
evaluation/const-fold only, 1 = cheap local peepholes, 2 = everything that can
grow the DAG.

### 1.4 `flatten_and` — split top-level conjunctions into separate assertions

`[C: src/preprocess/pass/flatten_and.cpp:30-67]`. Default **on**
`[C: src/option/option.cpp:523-527]`.

Rule: if assertion `i` is `(and …)`, replace it with `true` and push each
**leaf of the maximal AND-spine** (with a visited set, so shared subtrees are
pushed once) as its own assertion, recording the original as `parent`.

This is not cosmetic. It is what makes every *other* pass work: `solve_eqs`-style
passes only look at top-level assertions, so an equality buried under an `and`
is invisible until this pass hoists it.

### 1.5 `variable_substitution` — the big one

`[C: src/preprocess/pass/variable_substitution.cpp]`, 1,380 lines, default
**on** `[C: option.cpp:538-542]`, run to its own inner fixpoint. This single pass
subsumes what Z3 splits into `solve-eqs`, `extract_eqs` and a slicing pass.

#### 1.5.1 Finding a substitution — the base cases

`find_substitution` `[C: variable_substitution.cpp:323-355]`:

```
(= x t)      => x := t          [x is a CONSTANT (i.e. a free symbol)]
(= t x)      => x := t          [x is a CONSTANT]
p            => p := true       [p is a Boolean CONSTANT, bare assertion]
(not p)      => p := false      [p is a Boolean CONSTANT]
otherwise    => try normalize_substitution_eq (below)
```

#### 1.5.2 Gaussian elimination over BV (`pp-variable-subst-norm-eq`, default **on**)

`normalize_substitution_eq` `[C: variable_substitution.cpp:155-189]`, built on
`get_linear_bv_term_aux` `[C: :37-151]`. This is the highest-leverage rule in the
file and it is worth stating precisely.

Goal: rewrite one side of an equality as `factor * x + rest` where `x` is a free
symbol and `factor` is **odd** (hence invertible mod 2^w). The recursive
decomposition, with a recursion bound of **100** `[C: :148]`:

```
~e             where e ~> (f, x, r)          =>  (-f, x, ~r)
                 [because ~e = -1 - e]
(bvadd e0 e1)  where e0 ~> (f, x, r)         =>  (f,  x, (bvadd e1 r))
(bvadd e0 e1)  where e1 ~> (f, x, r)         =>  (f,  x, (bvadd e0 r))
(bvmul c  e)   c a value with LSB set (ODD), e ~> (f,x,r)
                                             =>  (c*f, x, (bvmul c r))
(bvmul e  c)   symmetric
x  (a free symbol)                           =>  (1, x, 0)
anything else                                =>  FAIL
```

Then, for `(= lhs rhs)` where neither side is already a bare symbol
`[C: :160-163]`:

```
lhs ~> (factor, x, rest)   =>   x := (bvmul (bvsub rhs rest) (modinv factor))
rhs ~> (factor, x, rest)   =>   x := (bvmul (bvsub lhs rest) (modinv factor))
```

`modinv` is the 2-adic inverse (`factor.ibvmodinv()` `[C: :187]`), which exists
exactly because `factor` is odd. **This is Gaussian elimination over Z/2^w.**

> Delta vs. us: `crates/axeyum-rewrite/src/solve_eqs.rs` orients only
> `(= x t)` with `x` a bare variable (its own doc says so at lines 3-9). It has
> no linear form and no modular inverse. `(= (bvadd (bvmul 3 x) y) t)` does not
> eliminate `x` for us; it does for Bitwuzla.

#### 1.5.3 Inequality-derived partial substitution (`pp-variable-subst-norm-bv-ineq`, default **OFF**)

`normalize_substitution_bv_ineq` `[C: variable_substitution.cpp:205-321]`. A
bound on a variable against a **constant** pins its high bits, so the variable is
replaced by a **narrower fresh variable padded with the forced constant prefix**:

```
(bvult x c)  or (bvule x c)   , clz = count_leading_zeros(c), 0 < clz < w
   =>  x := (concat (_ bv0 clz) fresh_[w-clz])                     [:253-265]

(bvugt x c)  or (bvuge x c)   , clo = count_leading_ones(c), 0 < clo < w
   =>  x := (concat (_ ones clo) fresh_[w-clo])                    [:266-278]

(bvslt x c)  or (bvsle x c)   , c has MSB set (i.e. c is negative),
   clz = count_leading_zeros(c[w-2:0]), clz < w-1
   =>  x := (concat (min_signed_[clz+1]) fresh_[w-clz-1])          [:279-298]

(bvsgt x c)  or (bvsge x c)   , c has MSB clear,
   clo = count_leading_ones(c[w-2:0]), clo < w-1
   =>  x := (concat (max_signed_[clo+1]) fresh_[w-clo-1])          [:299-319]
```

`c` may also be `(bvnot v)` for a value `v`, in which case `c = ~v` is used
`[C: :244-247]`. Sidedness is handled by flipping the relation when the variable
is on the right (`get_subst_inv_ineq_kind`, `[C: :191-203]`).

This is **width reduction driven by bounds** and it is exactly the effect of
Z3's `reduce-bv-size`, obtained by a different route. Note Bitwuzla ships it
**off by default** `[C: option.cpp:557-563]` — worth an A/B before we turn our
version on.

#### 1.5.4 Concat splitting of equalities (always attempted)

`normalize_substitution_eq_bv_concat` `[C: :450-499]`, rule `_rw_eq_bv_concat`
`[C: :370-404]`:

```
(= (concat a_[n] b) c_[m])
  =>  (and (= ((_ extract m-1  m-n) (concat a b)) ((_ extract m-1  m-n) c))
           (= ((_ extract m-n-1  0) (concat a b)) ((_ extract m-n-1  0) c)))
```

applied **to fixpoint** (`rw_eq_bv_concat` loops until no change, `[C: :406-423]`),
and **guarded**: it only fires if, after rewriting, each of the four resulting
extracts either disappeared entirely or bottomed out on a `CONSTANT`
`[C: :389-396]`. Without that guard it just adds extract nodes.

The result is then walked: each conjunct of the form `(= x …)` /`x`/`(not x)`
/`(not (= …))` is collected and **pushed as a new top-level assertion**
`[C: :476-495, :655-666]`, where the base substitution finder picks it up next
round. This is how `(= (concat x y) c)` becomes two independent variable
definitions.

#### 1.5.5 Disequality normalization (`pp-variable-subst-norm-diseq`, default **OFF**)

`[C: :505-522]`: for **Boolean or 1-bit BV** only,
`(not (= x e))  =>  (= x (bvnot e))`, turning a disequality into a
substitutable equality. The source comment is worth quoting verbatim: *"This is
worse on FP, and overall does not yield an improvement."* `[C: :511]` — a
negative result recorded in the code. Do not spend effort here.

#### 1.5.6 Extract elimination / variable slicing

This is the piece we most clearly lack, and it is fully self-documented in
source. `collect_extracts` `[C: :542-557]` gathers, for every assertion of the
form `(= ((_ extract u l) X) t)` where `X` is a free symbol, the pair
`(extract, t)` keyed by `X`. Then `process_extracts` `[C: :1088-1176]`:

1. Group by variable; build `indices: (u,l) -> [terms]`.
2. `compute_non_overlapping(nm, width, indices)` `[C: :1204-1300]` — a
   **boundary-sweep partition of the bit axis**:
   - every range `[u:l]` contributes boundaries `l` and `u+1`;
   - sort + dedupe boundaries; consecutive pairs are the sub-ranges;
   - for each sub-range, collect terms from every original range covering it —
     exact match moves the term, wider match re-extracts it via `extract_terms`
     `[C: :559-596]`, which **composes nested extracts** rather than stacking
     them (`extract(u,l, extract(_,l'))` becomes `extract(u+l', l+l')`);
   - sort descending by upper bound; **return empty unless the sub-ranges tile
     `[width-1:0]` exactly** (`:1284-1297`). Partial coverage is rejected.
   - The worked example in the source comment: input `[7:0]->{a}, [5:2]->{b}`,
     boundaries `{0,2,6,8}`, output `[1:0]->{a[1:0]}, [5:2]->{b, a[5:2]},
     [7:6]->{a[7:6]}`.
3. For each sub-range, pick one representative term, preferring **values, then
   constants, then anything else** (`priority`, `[C: :1075-1084]`), tie-broken by
   node id for determinism; skip candidates that are `X` itself or an extract of
   `X`.
4. If **every** sub-range got a representative, build
   `X := (concat slice_hi … slice_lo)`, push `(= X concat)` as a new assertion,
   and register the substitution — after running existing substitutions through
   it and checking `is_direct_cycle` `[C: :1155-1174]`.

Stat counters `num_eq_elim_extracts` / `num_eq_elim_extracts_substs`
`[C: variable_substitution.h:162-163]` exist specifically to measure this.

#### 1.5.7 Cycle handling (the correctness core)

Two mechanisms, both needed `[C]`:

- `is_direct_cycle(var, term)` `[C: :985-1015]` — a DAG walk checking `var` does
  not occur in `term`. This is the classic occurs check.
- `remove_indirect_cycles(substs)` `[C: :868-984]` — a **topological order
  computation over the substitution map itself**, using a stack with markers for
  the first on-stack occurrence of each substituted constant, dropping
  substitutions that would close a cycle. Direct cycles are assumed already gone
  (`:878-879`).

Ordering discipline: before checking for a cycle, the candidate term is first
run through the **existing** substitutions (`process(term)`, `[C: :699]`), so
new substitutions can be added incrementally and the cycle check stays local.

#### 1.5.8 Incremental soundness caveat worth copying

`[C: :753-805]` — a substituted equality can only be **deleted** if the variable
does not occur in assertions from a *previous* `check-sat` call. Bitwuzla's
conservative solution: only `initial_assertions()` get full substitution; later
levels keep the defining equality and use `process(assertion, excl_var)` which
substitutes everything *except* that variable `[C: :1017-1073]`. If we ever make
our pipeline incremental, this is the trap.

### 1.6 `skeleton_preproc` — run the SAT solver on the Boolean abstraction

`[C: src/preprocess/pass/skeleton_preproc.cpp:89-216]`. Default **on**
`[C: option.cpp:533-537]`, but **once only, on the initial assertions**.

Algorithm:

1. Bit-blast every new assertion with `bv::AigBitblaster(true)` — the
   `bool_bv1_mode` flag `[C: src/solver/bv/aig_bitblaster.h:36]`, i.e. **BV atoms
   become AIG leaves**; only the Boolean skeleton is encoded.
2. CNF-encode into a **CaDiCaL instance**, with the top-level AND flattening
   that emits unit clauses (§1.9).
3. Call `solver->simplify()` — CaDiCaL's own preprocessing — with a
   `FixedAssignmentListener` attached `[C: :28-39]` that records every literal
   CaDiCaL fixes at level 0.
4. Map each fixed literal back to the term whose AIG leaf it is (via
   `bitblaster_cache()`), skipping AIG-internal nodes, and **push the
   corresponding term (or its negation) as a new top-level assertion**
   `[C: :183-213]`.

So it uses the SAT solver purely as a **propagation engine over the abstraction**
and lifts the units it derives back to the word level, where the other passes can
then act on them. Cheap, one-shot, and it feeds `variable_substitution` new
top-level equalities it could not have found syntactically.

`[I]` This is the pass with the best value-per-line ratio in the file (234 lines
including boilerplate) *if* you already have a SAT core and an AIG bit-blaster —
which we do.

### 1.7 `embedded_constraints`

`[C: src/preprocess/pass/embedded_constraints.cpp:32-98]`. Default **on**
`[C: option.cpp:518-522]`.

For every top-level assertion `A` (or `(not A)`), record the substitution
`A := true` (resp. `A := false`), then rewrite **the children of every
assertion** under that substitution map — deliberately not the assertion itself,
so `A := true` does not trivially erase `A` (`:76-96`).

Effect: a formula asserted at top level is replaced by `true`/`false` wherever it
appears **nested inside another assertion**. Classic, cheap, and general — it is
not BV-specific at all.

Disabled when unsat cores or interpolants are requested `[C: :37-46]`.

### 1.8 `normalize` — AC normalization **gated by a bit-blasting cost model**

`[C: src/preprocess/pass/normalize.cpp]`, 1,777 lines. Default **on**
`[C: option.cpp:528-532]` but only at `rewrite_level >= 2` and only on the first
`check-sat`.

The transformations are AC-normalization of `bvadd`/`bvmul`/`bvand` chains via an
**occurrence map** `OccMap = std::map<Node, Integer>`
`[C: src/preprocess/pass/normalize.h:26]` — flatten the operator chain to a
multiset of leaves with multiplicities, fold the constants, factor out common
subterms across the two sides of an equality (`compute_common_subterms`,
`[C: normalize.h:58]`), and rebuild.

**The architecturally interesting part is not the rules, it is the accept test.**
`[C: normalize.cpp:1251-1382]`:

1. Compute candidate `assertions_pass1` (the normalized form).
2. Compute candidate `assertions_pass2` = `normalize_adders(pass1)` (a further
   cross-assertion adder-chain normalization).
3. Build **three `AigScore` objects** `[C: normalize.cpp:48-88]` — one per
   candidate set plus the original — where the score is *the number of AIG AND
   gates* produced by a partial bit-blast (`d_bitblaster.num_aig_ands()`).
4. Advance all three **incrementally** in 100,000-AND-gate slices
   (`AigScore::process(limit)`, `[C: :90-102]`) and stop as soon as the answer is
   known: a candidate that finishes below the original's current partial score
   wins; if the original finishes first, nobody won `[C: :1323-1346]`.
5. **Only replace the assertions if the winning score is strictly smaller**
   (`replace_assertions = size_after < size_before`, `[C: :1360-1361]`).

The scoring bit-blaster is deliberately partial: `bvudiv`/`bvurem` and everything
else not in its switch are abstracted as fresh AIG constants because "bit-blasting
them is expensive and the preprocessing pass does not normalize these operators"
`[C: :230-232]`. Squares get a cheaper encoding `[C: :183-191]`. Scoring is
**switched off entirely** the moment a bit-vector wider than 64 is seen
`[C: :1398-1403]`.

`[I]` This is the single most transferable idea in the whole Bitwuzla
preprocessor and it is not a rewrite rule: **a normalization pass whose rules
can go either way should propose candidates and let an AIG-gate-count oracle
choose, with an interruptible budget.** We already have an AIG with structural
hashing (`crates/axeyum-aig`), so the oracle is nearly free for us.

### 1.8.1 `normalize_adders` — cross-assertion adder-chain restructuring

`[C: src/preprocess/pass/normalize.cpp:1596-1718; collect_adders at :1719-1747]`.
Candidate "pass 2" in §1.8 is built by this routine. It walks **all** assertions,
collects every `bvadd` chain as an occurrence multiset over its leaves
(`compute_occurrences_add`), drops zero-count entries, then builds two indexes:
element -> the chains it occurs in, and chain -> its size. Chains are assigned
ids in descending size order, and every element gets the **sorted vector of chain
ids it participates in**. `[I]` Grouping elements by identical chain-id vectors is
what lets a shared sub-sum be materialized once and reused across several adder
chains -- i.e. this is Bitwuzla's answer to Z3's `max_bv_sharing`, restricted to
adders. It is expensive enough that it only ever runs as a *candidate* whose AIG
score must beat both the original and pass 1.

### 1.9 Bit-blasting side: AIG rewriting and the AIG→CNF encoder

Not preprocessing passes, but the same "destroy less information" family.

**`AigManager::rewrite_and`** `[C: src/lib/bitblast/aig/aig_manager.cpp:177-400]`
is the Brummayer–Biere local two-level minimization, explicitly graded into four
optimization levels, applied on *every* AND construction, with a `continue`-driven
loop so a level-3 substitution re-enters the rule set:

| Level | Rule | Shape | Condition | Result |
|---|---|---|---|---|
| 1 | Neutrality | `a ∧ 1` | | `a` |
| 1 | Idempotence | `a ∧ b` | `a = b` | `a` |
| 1 | Boundedness | `a ∧ 0` | | `0` |
| 1 | Contradiction | `a ∧ ¬b` | `a = b` | `0` |
| 2 | Contradiction (asym) | `(a∧b) ∧ c` | `a=¬c ∨ b=¬c` | `0` |
| 2 | Contradiction (sym) | `(a∧b) ∧ (c∧d)` | `a=¬c ∨ a=¬d ∨ b=¬c ∨ b=¬d` | `0` |
| 2 | Subsumption (asym) | `¬(a∧b) ∧ c` | `a=¬c ∨ b=¬c` | `c` |
| 2 | Subsumption (sym) | `¬(a∧b) ∧ (c∧d)` | `a=¬c ∨ a=¬d ∨ b=¬c ∨ b=¬d` | `c∧d` |
| 2 | Idempotence (asym) | `(a∧b) ∧ c` | `a=c ∨ b=c` | `a∧b` |
| 2 | Resolution | `¬(a∧b) ∧ ¬(c∧d)` | `a=c ∧ b=¬d` (and 3 symmetric cases) | `¬a` |
| 3 | Substitution (asym) | `¬(a∧b) ∧ c` | `b=c` | rewrite to `¬a ∧ c`, **loop** |
| 3 | Substitution (sym) | `¬(a∧b) ∧ (c∧d)` | `b∈{c,d}` | rewrite to `¬a ∧ (c∧d)`, **loop** |
| 4 | Idempotence (sym) | `(a∧b) ∧ (c∧d)` | `a=c ∨ b=c` | rewrite to `(a∧b) ∧ d`, **loop** |

Line refs: L1 `:186-215`, L2 `:224-304`, L3 `:306-374`, L4 `:376-394`, then
operand normalization by `|id|` `:399-400`.

**`AigCnfEncoder`** `[C: src/lib/bitblast/aig/aig_cnf.cpp]`:

- Top-level encoding **flattens the positive AND spine** and emits one **unit
  clause per leaf** instead of a Tseitin variable for the root `[C: :46-83]`.
- `is_ite` `[C: :170-242]` pattern-matches the two-level AIG shape
  `¬(c ∧ ¬a) ∧ ¬(¬c ∧ ¬b)` in all four commutative arrangements and emits the
  4-clause ITE encoding instead of 3+3+3 AND clauses `[C: :303-318]` — but
  **refuses if either inner node has more than one parent** (`parents() > 1`,
  `:182-198`), i.e. never destroys sharing to save clauses.
- Source carries explicit TODOs for n-ary AND and native XOR encodings
  `[C: :300-301]` — i.e. Bitwuzla has *not* done those.

> **We are ahead here, do not "fix" it.** `crates/axeyum-cnf/src/lib.rs` already
> has `encode_xor_gate` (:3718), `encode_not_ite_gate` (:3751),
> `encode_and_tree_gate` (:3887) and `encode_not_and_reverse` (:3822) — the two
> optimizations Bitwuzla leaves as TODOs. Ours is also **polarity-aware**:
> `encode_and_tree_gate` takes separate `encode_forward` / `encode_reverse`
> flags (`:3887-3892`), i.e. Plaisted–Greenbaum, where Bitwuzla always emits both
> directions of every AND (`aig_cnf.cpp:319-335`). And we already have the same
> **sharing guard** Bitwuzla uses (refuse the gate extraction when an inner
> helper node has more than one parent): `plan_xor_and_not_ite_gates` requires
> `use_counts[helper] == 1` for every helper (`crates/axeyum-cnf/src/lib.rs:3519-3545`,
> counts from `node_use_counts` at `:3483`), matching
> `aig_cnf.cpp:182-198`. **Nothing to borrow here.**

### 1.10 `elim_udiv` — present but **disabled**

`[C: src/preprocess/pass/elim_udiv.cpp:48-135]`, wired into the driver behind
`if (false && options.pp_elim_bv_udiv())` `[C: preprocessor.cpp:355-356]` with
the comment "Disabled until murxla-c598aa85aefc51a0.min.smt2 is fixed". Default
option is also `false` `[C: option.cpp:513-517]`.

The encoding it *would* apply is still worth recording, since it is the standard
one and we have our own `int_divmod.rs` analogue:

```
(bvudiv a b) => q,  (bvurem a b) => r,   q, r fresh, shared per (a,b) pair
  and assert:
    b ≠ 0  =>  q*b + r = a
    b ≠ 0  =>  r <u b
    b = 0  =>  q = ones
    b = 0  =>  r = a
    ¬ umulo(q, b)
    ¬ uaddo(q*b, r)
```

`[C: :88-107]`. `q` and `r` are cached on the canonical `(bvudiv a b)` /
`(bvurem a b)` key so a `udiv`/`urem` pair shares them `[C: :137-169]`.

### 1.10b `quant` — the cross-division pass we underweight

`[C: src/preprocess/pass/quant.cpp:33-60 (apply), :62-130 (process)]`. Default
**on** `[C: option.cpp:564-568]`. Three things happen in one bottom-up walk:

1. **Binder uniquification** — every `FORALL` whose bound variable id has been
   seen before gets a fresh variable (`:88-105`). The source notes the parser
   already guarantees this and the pass exists because the **API** does not.
2. **Inverse-based quantifier elimination** — `eliminate(res)` (`:107-115`,
   body at `:379-420`), i.e. BV-generalized destructive equality resolution
   (§5.2b).
3. **Alpha-normalization** — `alpha_normalize` (`:456-`), gated by
   `pp_quant_alpha`, default **on** `[C: option.cpp:569-574]`, which maps every binder to *the*
   canonical variable of its type (recycled through
   `get_canonical_var`/`release_canonical_var`, `:423-455`) so that
   alpha-equivalent quantifiers become literally the same interned node.

Point 3 is the one to note: we already have alpha-equivalence machinery
(`crates/axeyum-rewrite/src/alpha.rs`, 942 lines) but it is used as a *checker*,
per the sibling survey's table. Bitwuzla uses the same idea as a **normalizer**,
so alpha-equivalent subformulas share structure through the whole solver, not
just compare equal on demand. Checked: `alpha.rs` exports exactly two functions,
`alpha_equivalent` (`:101`) and `alpha_equivalent_to_negation` (`:132`) — both
predicates. **There is no normalizing entry point.** Adding one (rename every
binder to the canonical variable of its type, then let interning do the sharing)
turns an `O(n²)` pairwise comparison into `O(n)` hash-consing, and it reuses the
comparison logic that already exists and is already tested.

### 1.11 What Bitwuzla does **not** have

`[C]` A repository-wide grep for `unconstrained|uncnstr` across
`references/bitwuzla/src/**.{cpp,h}` returns **no preprocessing pass** — only
`bitvector_domain.h` (propagation-based local search) and two unrelated
comments. **Bitwuzla has no unconstrained-variable elimination pass.** Boolector
did (`ucopt`); the 2.x rewrite dropped it. `[I]` Either it was subsumed by the
rewriter + variable substitution, or it was not worth the model-reconstruction
machinery. Either way, do not treat "Bitwuzla does it" as the justification for
expanding ours — Z3 is the reference there (§2).

### 1.12 Adjacent, and probably the biggest QF_BV lever of all: the abstraction module

Not in `src/preprocess/`, but it decides how much ever gets bit-blasted.
`[C: src/solver/abstract/]`.

- **On by default** (`abstraction = true`), threshold
  `abstraction_bv_size = 33` `[C: option.cpp:364-376]`.
- Abstracts `BV_MUL`, `BV_UDIV`, `BV_UREM` (and optionally `BV_ADD` and `ITE`)
  whose operand width is `>= 33` `[C: abstraction_module.cpp:56-79, :303-307]`,
  replacing the term with a fresh variable.
- Refinement is **not** "add the exact definition". It is a **graded ladder of
  cheap partial lemmas** — counted from `enum LemmaKind`
  `[C: src/solver/abstract/abstraction_lemmas.h]`: **19 `MUL*`, 37 `UDIV*`,
  15 `UREM*` and 13 `ADD*` kinds**, each family also carrying a `*_VALUE`
  instantiation rule — e.g.

  ```
  MUL1_POW2      (=> (= s 2^i) (= t (bvshl x i)))
  MUL3_IC        (= (bvand (bvor (bvneg s) s) t) t)          -- invertibility condition
  MUL4_ODD       (= (extract 0 0 t) (bvand (extract 0 0 x) (extract 0 0 s)))
  UDIV3          (=> (= s 0) (= t ones))
  UDIV5          (=> (distinct s 0) (bvule t x))
  UREM2          (=> (distinct s 0) (bvult t s))
  ```

  plus **value instantiations** (instantiate the lemma at the model's concrete
  values), with `abstraction_value_limit = 8` meaning `bv_size/8` value
  instantiations before finally falling back to the full
  `BITBLAST_BV_MUL` / `BITBLAST_BV_UDIV` / `BITBLAST_BV_UREM` lemma
  `[C: abstraction_module.cpp:417-486, option.cpp:382-394]`.
- There is a **lemma scorer** (`abstraction_lemma_scorer.cpp`) selecting which
  lemmas to try first.

> **We have the skeleton but not the ladder.** `crates/axeyum-solver/src/lazy_bv.rs`
> abstracts `bvmul`/`bvudiv`/`bvurem`/`bvsdiv`/`bvsrem`/`bvsmod` by fresh
> variables and refines with the **exact** `fresh == op(lhs,rhs)` constraint
> (its doc header, lines 1-27) — i.e. we jump straight to Bitwuzla's
> last-resort lemma. And `SolverConfig::lazy_bv` is **off by default**
> (`crates/axeyum-solver/src/backend.rs:224-232`), where Bitwuzla's is on.



---

## 2. Z3: three pipelines, the `ast/simplifiers` framework, and the rule tables

Read from `references/z3` @ `e18d63bd`. This is the section the existing surveys
do not cover: they document `src/ast/rewriter/`; this is `src/ast/simplifiers/`,
`src/tactic/bv/`, and `src/ast/converters/expr_inverter.cpp`.

### 2.0 There are THREE preprocessing pipelines, and they do not agree

This is the first thing to get right; the folklore treats "the QF_BV tactic" as
if it were the only path.

| Pipeline | Entry point | Used when |
|---|---|---|
| **(a) tactic pipeline** (2012) | `mk_qfbv_tactic` `[C: src/tactic/smtlogics/qfbv_tactic.cpp:126]` | `(check-sat)` through `smt_strategic_solver` when a tactic is selected `[C: src/tactic/portfolio/smt_strategic_solver.cpp:70-71]` |
| **(b) `dependent_expr_simplifier` chain** (2022) | `init_preprocess` `[C: src/solver/solver_preprocess.cpp:48-90]` | `simplifier_solver` `[C: src/solver/simplifier_solver.cpp:226]`, `sat.smt=true`, and `Z3_solver_add_simplifier` |
| **(c) `asserted_formulas`** (legacy smt kernel) | `asserted_formulas::reduce` `[C: src/solver/assertions/asserted_formulas.cpp:270-318]` | inside `smt::context` |

Pipeline (c) has **neither `solve_eqs` nor `elim_unconstrained`**. Pipeline (b)
has no `bv_size_reduction` and no `ackermannize`. Only (a) carries the
QF_BV-tuned parameters. And there is a fourth, thinnest path: for `QF_BV` with
`hi_div0` (the default), `mk_solver_for_logic` returns `mk_inc_sat_solver`
`[C: smt_strategic_solver.cpp:144-145]`, whose chain
`[C: src/sat/sat_solver/inc_sat_solver.cpp:755-795]` is

```
simplify → propagate-values → card2bv
  → simplify{som, pull_cheap_ite, local_ctx, flat, elim_and, blast_distinct}
  → max-bv-sharing → bit-blast → simplify{flat:false}
```

with **no `solve_eqs`, no `elim_unconstrained`, no `reduce-bv-size`, no
`bv-divrem-bounds`**. `[I]` If you want "what Z3 actually runs on an incremental
QF_BV query", that is it.

### 2.1 The default QF_BV preamble

Verbatim `[C: qfbv_tactic.cpp:37-89]`, verified by direct read:

```
1.  simplify           {flat_and_or:false}
2.  propagate-values   {flat_and_or:false}
3.  solve-eqs          {solve_eqs_max_occs: 2}   // "conservative gaussian elimination"
4.  elim-uncnstr                                  // THE OLD TACTIC, see 2.2
5.  bv-divrem-bounds
6.  reduce-bv-size     [if_no_proofs(if_no_unsat_cores(...))]
7.  simplify           {som:true, pull_cheap_ite:true, push_ite_bv:false,
                        local_ctx:true, local_ctx_limit:1e7, flat:true,
                        hoist_mul:false, flat_and_or:false}
8.  simplify           {hoist_mul:true, som:false, flat_and_or:false}
9.  max-bv-sharing
10. ackermannize_bv    [if_no_proofs(if_no_unsat_cores(...))]
```

with `main_p` setting `elim_and:true, push_ite_bv:true, blast_distinct:true`
downstream `[C: :83-89]`. Steps 7 and 8 are **mutually exclusive normal forms
applied back to back** — `som` and `hoist_mul` are asserted incompatible
(`SASSERT(!m_som || !m_hoist_mul)` `[C: src/ast/rewriter/poly_rewriter.h:107]`)
— i.e. "distribute fully, then re-factor". The only cost-vs-benefit comment in
the file is on step 8 `[C: :71-76]`:

> Z3 can solve a couple of extra benchmarks by using hoist_mul but the timeout in
> SMT-COMP is too small. Moreover, it impacted negatively some easy benchmarks.
> We should decide later, if we keep it or not.

After the preamble `[C: :103-118]`: `bit-blast`, then (only when memory < 300 MB)
`simplify; solve-eqs` **again, on the Boolean structure after blasting**, then
`aig`, then `sat`.

QF_AUFBV/QF_ABV `[C: qfaufbv_tactic.cpp:32-58]`: same shape, no `hoist_mul`
pass, `sort_store:true` added. `reduce_args` is present but **commented out with
a soundness question**: `// sound to use? if_no_proofs(if_no_unsat_cores(...))`
`[C: :47]`.

### 2.2 Two `elim_unconstrained` implementations, and the tactic uses the old one

- **New**: `src/ast/simplifiers/elim_unconstrained.cpp` (478 lines) + the rule
  set in `src/ast/converters/expr_inverter.cpp` (1083 lines).
- **Old**: `src/tactic/core/elim_uncnstr_tactic.cpp` (1116 lines).
  **`mk_elim_uncnstr_tactic` is what step 4 of the QF_BV preamble calls**
  `[C: qfbv_tactic.cpp:66]` — verified by direct read.

The header of the new file states exactly why it was rewritten
`[C: elim_unconstrained.cpp:10-21]`:

> `elim_unconstr_tactic` has some built-in limitations […] it is inefficient for
> examples like `x <= y, y <= z, z <= u, ...`. All variables x, y, z, .. can
> eventually be eliminated, but the tactic requires a **global analysis between
> each elimination**. We address this by using reference counts and maintaining a
> heap of reference counts. […] it does not accommodate side constraints. […] it
> is not modular: we detach the expression inversion routines to self-contained
> code.

**That paragraph is a description of our current implementation.**
`crates/axeyum-rewrite/src/elim_unconstrained.rs:344-360` recomputes the whole
occurrence map after every single elimination.

#### Occurrence counting — old (recount the world)

`collect_occs` `[C: src/tactic/core/collect_occs.cpp:25-42]` is two mark sets
over the hash-consed DAG; the unconstrained set is
`{v : v ∈ m_vars ∧ ¬more_than_once(v)}` `[C: :88-91]`. Because the DAG is
hash-consed, `visit(child)` counts **distinct parent edges**, not tree
occurrences: `(bvadd x x)` marks `x` twice; a shared `f(x)` used in ten places
contributes one. The tactic then loops `[C: elim_uncnstr_tactic.cpp:983-1025]`:
rewrite everything, and if anything changed, **drop the rewriter cache, reset the
variable set, and re-run `collect_occs` over the entire goal**.

#### Occurrence counting — new (persistent node graph + refcount heap)

`node` `[C: elim_unconstrained.h:27-68]`: `m_term`, `m_proof`, `m_dirty`,
`m_parents: ptr_vector<node>` (parent **list**, not a count), `m_root` (union-find
style), `m_top`. Documented invariants `[C: elim_unconstrained.cpp:45-91]`
include `parents(root(n)) = ⋃ parents of the class` and **"the depth of a parent
is always greater than the depth of a child"** — which is what makes
`reconstruct_terms` a depth-sorted single pass `[C: :366-376]`.

The unconstrained predicate is a **closure installed into the inverter**
`[C: :124-127]`, with five conjuncts:

```cpp
// the space after [&] is mine; without it check-links.sh reads the
// lambda as a markdown link. Otherwise verbatim.
is_var = [&] (expr* e) {
    return is_uninterp_const(e) && !m_fmls.frozen(e) && !m_disabled.is_marked(e)
        && get_node(e).is_root() && get_node(e).num_parents() <= 1;
};
```

The worklist is a **min-heap ordered by parent count**
(`is_var_lt` `[C: :134-138]`), and the loop `[C: :140-197]` is:

```
while heap not empty:
    v = heap.erase_min(); n = node(v)
    if !n.is_root() || n.is_top() || n.num_parents() == 0  -> continue
    if n.num_parents() > 1                                 -> RETURN   (not continue)
    p = n.parent()
    if !is_child(n,p) || !p.is_root() || p not ground app   -> continue
    inverted = m_inverter(p.decl, rebuilt args, out r)
    if !inverted -> continue
    set_root(p, root(r))                       # p's class now maps to r
    if r is an uninterpreted const: heap.insert(r)   # THE CASCADE
    else: m_created_compound = true
```

Three mechanisms make the cascade work, and all three are things we lack:

1. **`set_root(n, r)` transplants the parent list** —
   `r.add_parents(n.parents()); n.set_root(r); …` `[C: :199-208]`. When
   application `p` is replaced by fresh `r`, `r` inherits `p`'s parents, so if
   `p` had one parent, `r` is immediately a live candidate. That is precisely
   the `x ≤ y, y ≤ z, z ≤ u` chain the design note calls out.
2. **`return`, not `continue`, at `num_parents > 1`.** Because the heap is
   min-ordered on parent count, a minimum above 1 means nothing remains, so the
   round is over. This is why it is a heap and not a queue.
3. **`invalidate_parents`** `[C: :210-227]` marks an upward dirty closure;
   `reconstruct_term` `[C: :313-361]` rebuilds only dirty roots, bottom-up on an
   explicit stack.

The outer loop is capped at **3 rounds** and repeats only if
`m_created_compound` `[C: :441-455]` — i.e. only when some replacement was a
compound term (the `x*K` rule below), because pure fresh-variable replacements
are fully handled by the intra-round cascade.

`elim_unconstrained` **does not support proofs**: it builds proof objects but
never attaches them (`assert_normalized` passes `nullptr` `[C: :389]`), the header
says *"proof production is work in progress"* `[C: :41-43]`, and
`supports_proofs()` is not overridden — so the tactic driver **skips the pass
entirely when proofs are on** `[C: src/tactic/dependent_expr_state_tactic.h:133]`.

### 2.3 `expr_inverter`: a per-theory plugin registry

`[C: src/ast/converters/expr_inverter.h:22-60]`

```cpp
class iexpr_inverter {
    std::function<bool(expr*)>  m_is_var;   // INJECTED unconstrained-ness predicate
    generic_model_converter_ref m_mc;       // where model defs are recorded (OPTIONAL)
    bool uncnstr(expr*) / uncnstr(num, args);
    void mk_fresh_uncnstr_var_for(sort*, expr_ref&);
    void add_def(expr* v, expr* def);
    void add_defs(num, args, u, identity);  // args[0] := u, rest := identity
  public:
    virtual bool operator()(func_decl* f, unsigned n, expr* const* args, expr_ref&) = 0;
    virtual bool mk_diff(expr* t, expr_ref& r) = 0;   // a term guaranteed != t
    virtual family_id get_fid() const = 0;            // WHICH THEORY
};
```

`expr_inverter` holds a `ptr_vector<iexpr_inverter>` **indexed by family id** and
dispatches on the operator's theory `[C: expr_inverter.cpp:1027-1042]`.
Registered `[C: :1012-1024]`: `arith, bv, array, datatype, basic, seq,
finite_set`; `pb` is `#if 0`-ed `[C: :755-831]`.

Four decisions worth copying:

- **`m_is_var` is injected.** The occurrence analysis lives in the pass; the
  inversion rules live per theory and never learn how "unconstrained" was
  decided. That is what lets one component serve several passes.
- **`m_mc` is optional.** Every rule reads "always compute the replacement,
  record the model definition **only if** a converter is attached"
  (`if (m_mc) add_def(...)`). Our trail is unconditional.
- **`mk_diff(t) -> r` with `r != t` is first-class**, because the equality rule
  needs it, and it is **sort-specific**: Bool → `not t` `[C: :142-146]`;
  arith → `t + 1` `[C: :258-262]`; BV → `bvnot t` `[C: :599-603]`;
  array → `store(t, i…, d)` with `d = mk_diff(select(t, i…))`, a **recursive**
  call back through the top-level inverter `[C: :652-677]`; datatype → wrap `t`
  in a recursive constructor `[C: :721-752]`; seq → `t ++ "a"` `[C: :957-963]`.
- **`mk_diff` carries the soundness guard** `[C: :1043-1063]`:

  ```cpp
  if (!m.is_fully_interp(s)) return false;
  sort_size sz = s->get_num_elements();
  if (sz.is_finite() && sz.size() <= 1) return false;   // unsound on a 1-element sort
  ```

  The old tactic explains why `[C: elim_uncnstr_tactic.cpp:239-254]`:
  > `(forall ((x S) (y S)) (= x y))` / `(not (= c1 c2))` — The constants c1 and
  > c2 have only one occurrence in the formula above, but they are not really
  > unconstrained. The quantifier forces S to have interpretations of size 1.

  **This is the trap to write a soundness-negative test for.**

### 2.4 The complete rule table

Notation: `x`, `x'` satisfy `uncnstr(·)`; `t`, `s` arbitrary; `u`/`fresh` a new
constant, **hidden in the model converter at creation** `[C: :986-990]`;
`:=` a recorded model definition. Every `add_def` is a no-op when `m_mc` is null.

#### Booleans / core — `basic_expr_inverter` `[C: :27-147]`

| Rule | Side condition | Defs | line |
|---|---|---|---|
| `(ite c x x') => u` | both branches unconstrained | `x := u`, `x' := u` | `:92-97` |
| `(ite x x' e) => u` | cond + then | `x := true`, `x' := u` | `:98-103` |
| `(ite x t x') => u` | cond + else | `x := false`, `x' := u` | `:104-109` |
| `(not x) => u` | | `x := not u` | `:111-118` |
| `(and x₁…xₙ) => u` | **all** | `x₁ := u`; `xᵢ := true` | `:119-125` |
| `(or x₁…xₙ) => u` | **all** | `x₁ := u`; `xᵢ := false` | `:126-132` |
| `(= x t) => u` | one side, `mk_diff(t)` succeeds | `x := ite(u, t, diff(t))` | `:30-49, :133-135` |

The `(= x t)` rule is the one to stare at: an equality with an unconstrained side
is a **free Boolean**, witnessed by "if the fresh bit is true make them equal,
else make them differ". It is not BV-specific and it deletes a whole comparator.

#### Arithmetic — `arith_expr_inverter` `[C: :149-263]`. **QF_LIA / QF_LRA / QF_IDL / QF_NIA / QF_NRA.**

| Rule | Side condition | Defs | line |
|---|---|---|---|
| `(+ t₁ … x … tₙ) => u` | **any one** operand unconstrained | `x := u − Σ_{j≠i} tⱼ` (or `x := u` if alone) | `:181-210` |
| `(* x₁…xₙ) => u` | **all** | `x₁ := u`; `xᵢ := 1` | `:216-221` |
| `(* c x) => u` | `c` a numeral, **not integer**, `c ≠ 0` | `x := (1/c)·u` | `:225-234` |
| `(<= x t) => u` | | `x := ite(u, t, t+1)` | `:157-179, :246-248` |
| `(<= t x) => u` | | `x := ite(u, t, t−1)` | `:160-178` |
| `(>= x t) => u` | | `x := ite(u, t, t−1)` | `:249-251` |
| `(>= t x) => u` | | `x := ite(u, t, t+1)` | `:160-178` |

Two notes. **`+` needs only one unconstrained operand where `*` needs all** —
that asymmetry is the highest-yield line in the table. And the `*` rule is
**reals only** (`!is_int`), because `c·x` cannot hit every integer. The `<=`
rules need **no side constraint** because the order is unbounded — unlike BV
(below), which is exactly why the BV versions are harder.

#### Bit-vectors — `bv_expr_inverter` `[C: :265-604]`, dispatch at `:545-597`

| Rule | Side condition | Defs | line |
|---|---|---|---|
| `(bvadd t₁ … x … tₙ) => u` | any one | `x := bvsub(u, Σ rest)` | `:268-297` |
| `(bvmul x₁…xₙ) => u` | **all** | `x₁ := u`; `xᵢ := 1` | `:302-308` |
| `(bvmul c x) => u` | `c` **odd** | `x := bvmul(c⁻¹, u)` | `:310-321` |
| `(bvmul K x) => concat(u[sz−sh−1:0], 0^sh)` | `K > 0` even, `sh` = trailing zeros, `J = K >> sh` | `x := bvmul(J⁻¹, r)` | `:330-352` |
| `(bvudiv/bvsdiv x x') => u` | **both** | `x := u`, `x' := 1` | `:394-405` |
| `x[hi:lo] => u` | full width | `x := u` | `:377-381` |
| `x[hi:lo] => u` | proper sub-range | `x := concat(0^{sz−hi−1}, u, 0^{lo})`, empty blocks omitted | `:382-390` |
| `(concat x₁…xₙ) => u` | **all** | walking from LSB, `xᵢ := u[low+szᵢ−1 : low]` | `:407-426` |
| `(bvule x t) => (or u (= t MAX))` | lhs | `x := ite(r, t, t+1)`, `r` = the **whole disjunction** | `:442-459` |
| `(bvule t x) => (or u (= t MIN))` | rhs | `x := ite(r, t, t−1)` | `:460-476` |
| `(bvsle …)` | as above with signed `MAX`/`MIN` | | same |
| `(bvule/bvsle x x') => u` | both | `x := ite(u, 0, 1)`, `x' := 0` | `:430-441` |
| `(bvnot x) => u` | | `x := bvnot u` | `:480-487` |
| `(bvor x₁…xₙ) => u` | **all** | `x₁ := u`; `xᵢ := 0` | `:572-580` |
| `(bvand x₁…xₙ) => u` | **all** | `x₁ := u`; `xᵢ := ones` | `:581-589` |
| `(bvshl/bvashr/bvlshr x x') => u` | **both** | `x := u`, `x' := 0` | `:489-499` |

**The `bvule`/`bvsle` rules are the "side constraints" the design note referred
to**: `r = mk_or(fresh, mk_eq(t, MAX))` `[C: :455]`, because `x ≤ t` is *not*
universally satisfiable — it fails when `t` is already the maximum. The old
tactic flags this as an open item `[C: elim_uncnstr_tactic.cpp:596-598]`:
*"The result of bv_le is not just introducing a new fresh name, we need a side
condition. TODO: the correct proof step"*.

The even-multiplier rule is **the only rule returning a compound BV term**, and
is what sets `m_created_compound` and buys another outer round. Its correctness
argument, verbatim `[C: :323-328]`: *"x * K -> fresh[hi-sh-1:0] ++ 0…0 where
sh = parity of K, then x -> J^-1*fresh where J = K >> sh. Because x * K =
fresh * K * J^-1 = fresh * 2^sh"*.

**Explicit non-coverage**, verified by extracting the switch cases: there is
**no rule** for `bvcomp`, `bvneg`, `bvxor`, `bvsub`, `bvurem`/`bvsrem`/`bvsmod`,
`zero_extend`, `sign_extend`, `rotate`, `bvult`/`bvslt`, `bvredor`/`bvredand`.
`[I]` For the strict comparisons that is fine (the `bv_rewriter` normalizes them
to negated non-strict first). For `bvneg`, `bvxor`, `bvsub`, `bvcomp` it is a
genuine gap — and **we already have `bvneg`, `bvxor` and `bvsub`** in
`elim_unconstrained.rs`, so on those three operators we are ahead of Z3.

#### Arrays `[C: :617-678]`, datatypes `[C: :682-753]`, sequences `[C: :875-965]`, finite sets `[C: :833-873]`

| Rule | Side condition | Defs |
|---|---|---|
| `(select x i…) => u` | **array** operand unconstrained | `x := ((as const A) u)` |
| `(store x i… x') => u` | array **and** stored value | `x' := (select x i…)` **first**, then `x := u` |
| `(acc x) => u`, `acc` an accessor of ctor `C` | operand unconstrained; every field sort of `C` fully interpreted | `x := C(…, u at acc's slot, some_value elsewhere)` |
| `(str.++ x₁…xₙ) => u` | all | `x₁ := u`; `xᵢ := ""` |
| `(str.contains x t) => (or u (str.is_empty x))` | lhs | `x := ite(u, t, "")` |
| `(str.contains t x) => u` | rhs | `x := ite(u, t, t ++ t ++ "a")` |
| `(str.in_re x R) => u` | `R` ground; witnesses `s₁ ∈ R`, `s₂ ∈ ¬R` both found | `x := ite(u, s₁, s₂)` |
| `(union x y) => x` / `(intersect x y) => x` | both unconstrained | `y := x` |

**The array `store` definition order is load-bearing.** `x'` is defined first, in
terms of the *original* `x`; `generic_model_converter` applies ADDs in **reverse
insertion order** `[C: src/ast/converters/generic_model_converter.cpp:48]`, so
`x` gets its value before `x'`'s definition is evaluated. Getting this backwards
silently produces wrong models — exactly the class of bug our replay-against-the-
original discipline would catch, and worth an explicit test.

The finite-set rules are the only ones in the file that return an **existing
argument** rather than a fresh constant.

#### Old-tactic delta

The old tactic's BV switch `[C: elim_uncnstr_tactic.cpp:681-730]` covers only
`BADD, BMUL, BSDIV/BUDIV, SLEQ, ULEQ, CONCAT, EXTRACT, BNOT, BOR`. It **lacks
`bvand`, all three shifts, and the even-multiplier rule.** `[I]` So on a QF_BV
benchmark the *tactic* pipeline — the one actually used — is strictly weaker on
this pass than the simplifier pipeline.

### 2.5 Model reconstruction: loose vs rigid, and why it matters for incrementality

Two layers. The inverter writes `generic_model_converter` entries
(`{decl, def, HIDE|ADD}` `[C: generic_model_converter.h:26-33]`, applied
**backwards** `[C: .cpp:38-95]`). `elim_unconstrained::update_model_trail`
`[C: :393-424]` then transcribes them into the framework's
`model_reconstruction_trail`, walking the entries **in reverse with a growing
`expr_replacer`** so the chain of definitions composes into one flat,
self-contained substitution.

The critical flag is the last argument:

```
trail.push(sub, old_fmls, /*replay_constraints=*/true);   // elim_unconstrained -> LOOSE
trail.push(save_subst({}))                                // solve_eqs Gaussian -> RIGID
```

`[C: elim_unconstrained.cpp:~420, solve_eqs.cpp:259]`. Loose vs rigid is decided
**purely by whether the removed-formula list is empty** `[C:
model_reconstruction_trail.h:67]`, and it changes replay behaviour
`[C: model_reconstruction_trail.cpp:89-98]`:

- **Loose** (satisfiability-preserving only): if a *later* incremental assertion
  mentions an eliminated symbol, the **original formulas are resurrected** and
  the trail entry is deactivated.
- **Rigid** (equivalence-preserving, e.g. a solved equality): the substitution is
  instead pushed **forward** onto the new assertions `[C: :157-192]`.

A fast path guards all of it: collect the free variables of the new assertions
and return immediately if none intersects the set of decls ever used as a trail
key `[C: :47-62]`.

`[I]` **Our `ModelReconstructionTrail` has one entry kind (`Define`) and no
loose/rigid distinction.** That is correct today because our pipeline is
one-shot, but it is exactly the thing that must exist before preprocessing can be
incremental — and it is a cheap field to add now rather than a refactor later.

### 2.6 The pass framework contract

`[C: src/ast/simplifiers/dependent_expr_state.h]`

- **`dependent_expr`** `[C: :24-28]` — `{expr* fml; proof* proof; expr_dependency* dep}`
  with a structured-binding accessor, which is why every pass reads
  `auto [f, p, d] = m_fmls[i]();`. `dep` is a hash-consed AND-set of tracked
  assumption literals.
- **`dependent_expr_state`** `[C: :45-105]` — pure virtuals `qtail()`,
  `operator[]`, `update(i, de)`, `add(de)`, `inconsistent()`, `model_trail()`,
  `updated()`, `reset_updated()`; non-virtual `qhead()`, `frozen(f)`,
  `freeze_suffix()`, `push()`/`pop(n)`.
- **`qhead` is the already-dispatched, immutable prefix.** A pass touches only
  `[qhead, qtail)`. `advance_qhead()` `[C: :90]` is
  `freeze_prefix(); m_suffix_frozen = false; m_qhead = qtail();`.
- **`indices()`** `[C: :211-227]` — the iteration protocol: `operator++` re-reads
  `qtail()` (so a pass may `add()` while iterating) and short-circuits on
  cancellation and on `inconsistent()`. **No pass has to remember to check.**
- **Freezing is the substitute for a global liveness analysis.**
  `freeze_prefix()` freezes every decl in the dispatched prefix
  `[C: .cpp:97-101]`; `freeze_suffix()` `[C: .cpp:106-124]` freezes decls in
  recursive-function definitions, decls in the **dependency** expressions, and
  **only the `as-array` occurrences** in the formulas. Callers:
  `elim_unconstrained`, `solve_eqs`, `eliminate_predicates`, `reduce_args`.
- **`flatten_suffix()`** `[C: :161-190]`, run between every two passes: drop
  duplicates and `true`; split `(and a₁…aₙ)` into n assertions; split
  `(not (or a₁…aₙ))` into n negated assertions; compact. **This is Bitwuzla's
  `flatten_and` (§1.4), promoted into the framework itself.**
- **The pass interface** `[C: :231-246]` — only `name()` and `reduce()` are
  mandatory. `supports_proofs()` defaults `false` and is load-bearing: the
  tactic driver **skips a pass entirely when proofs are on and it returns false**
  `[C: src/tactic/dependent_expr_state_tactic.h:133]`.

**What the framework does NOT give you** — three absences worth knowing before
copying it:

- **No shared occurrence counts.** Every pass rolls its own:
  `solve_eqs::collect_num_occs` (dead, below), `propagate_values`'s
  `shared_occs`, `ctx_simplify_tactic`'s `goal_num_occurs`,
  `elim_unconstrained`'s node parent lists.
- **No shared rewriter.** Each pass owns a `th_rewriter` (`solve_eqs.h:51`,
  `propagate_values.h:35`, `eliminate_predicates.h:99`, `bound_simplifier.h:36`,
  `euf_completion.h:143`, `bv_slice.h:35`).
- **No fixpoint driver.** `then_simplifier` `[C: then_simplifier.h:70-91]` runs
  each child **exactly once, left to right**, with `flatten_suffix()` between,
  stopping early on inconsistency/cancellation. The only fixpoint-ish combinator
  is `if_change_simplifier` `[C: :132-141]`. Each pass instead runs its own
  bounded loop: **3** (`elim_unconstrained`), **20** (`solve_eqs`), **4**
  (`propagate_values`), **4** (`euf_completion`), **10** (dominator),
  **5** (`bound_simplifier`).

`[I]` Bitwuzla makes the opposite choice — one outer fixpoint over all passes
(§1.1) plus an inner loop for `variable_substitution` only. Our
`preprocess.rs` already does the Bitwuzla thing (8 rounds). The Z3 answer is
worth knowing but I would keep ours.

### 2.7 `solve_eqs` and `extract_eqs`

**The candidate type already carries the orientation**: `dependent_eq { expr*
orig; app* var; expr_ref term; expr_dependency_ref dep; }`
`[C: src/ast/simplifiers/extract_eqs.h:30-37]` — orienting is the *plugin's* job,
not a term order's. Three plugins, in priority order
`[C: extract_eqs.cpp:449-453]`: `arith`, `basic`, `bv`. **There is no datatype
plugin.**

Rules `[C: extract_eqs.cpp]`:

```
-- basic (:31-141)
(= x t) / (= t x)                              => x := t          [x uninterp const, x ∉ t]
(ite c (= x s) (= x t))                        => x := ite(c,s,t)
(or (and (= z s) a) (and (= z t) (not a)))     => z := ite(a,s,t)
(and (or (= z s) a) (or (= z t) (not a)))      => z := ite(a',s,t)
p / (not p)                                    => p := true/false [m_allow_bool]

-- arith (:222-447)
(= (+ .. z ..) Y)                    => z := Y − Σ_{j≠i} aⱼ
(= (+ .. (* −1 z) ..) Y)             => z := −(Y − Σ_{j≠i} aⱼ)
(= (+ .. (* c z) ..) Y)              => z := (Y − Σ)/c              [real, c≠0]
(= (* .. x ..) Y)                    => x := Y / Π_{j≠i} aⱼ         [real, others nonzero]
(= (mod u k) Y),  k > 0              => u := k·fresh + Y            [m_eliminate_mod]
(= (to_real z) (to_real u))          => z := u
(<= x k) with lower(x) == k          => treat as (= x k), deps joined

-- bv (:143-220)
(= (bvadd .. z ..) Y)                => z := Y − Σ_{j≠i} aⱼ
(= (bvadd .. (bvmul c z) ..) Y)      => z := c⁻¹·(Y − Σ)            [c odd]
(= (bvmul c z) Y)                    => z := c⁻¹·Y                  [c odd]
```

**The BV rules are the same Gaussian elimination Bitwuzla does (§1.5.2), reached
independently.** Two solvers converging on it is the strongest signal in this
document that we should have it.

**The occurs check is a DFS substitution-level numbering, not a Kahn sort and not
a per-candidate walk** `[C: solve_eqs.cpp:87-175]`. Each DFS root gets a fresh
level band; a candidate for variable `j` is rejected if any variable in its
definition already has `level < curr_level`. Strictly increasing levels along
"defines" edges ⇒ acyclic. `normalize()` `[C: :177-209]` then substitutes in
**descending level order**, so one pass yields an idempotent substitution.

**A dead knob to be aware of.** `collect_num_occs` is **never called** — verified
myself: `grep -rn collect_num_occs src/` returns only the two declarations, the
two definitions, and the internal call between the overloads. So `m_num_occs`
stays empty, `check_occs` always returns true, and **the
`solve_eqs_max_occs: 2` "conservative gaussian elimination" setting in the QF_BV
preamble currently does nothing** `[C: qfbv_tactic.cpp:40-41]`. Wire the
occurrence cap in ours; do not inherit the bug.

### 2.8 `propagate_values` — how it differs from rewriting

`[C: src/ast/simplifiers/propagate_values.cpp]`, 119 lines. The rewriter is
driven **with an attached substitution** (`m_rewriter.set_substitution(&m_subst)`
`[C: :82]`), so every subterm is looked up during the ordinary bottom-up rewrite
and the substitution's dependency is accumulated.

Facts `[C: :52-65]`, each guarded by `shared(t)` (appears more than once) — a
cost guard, since substituting a single-use term buys nothing:

```
unit (not a),  shared(a)               =>  a := false
unit f,        shared(f)               =>  f := true
unit (= v t) / (= t v), is_value(v)    =>  t := v
```

The loop `[C: :67-104]` is **forward then backward per round**, with
`init_sub()` rebuilding from scratch between the two directions, up to
`max_rounds = 4`. Forward+backward gives each formula the benefit of all others
in two passes; rebuilding between directions is essential or the backward pass
uses stale facts derived from formulas it is about to change.

`[I]` Ours (`propagate_values.rs`) is a forward fixpoint with a batched DAG
rebuild per round. Adding the backward sweep is a small change with a clear
argument behind it.

### 2.9 BV-specific size and structure reductions

**`reduce-bv-size`** `[C: src/tactic/bv/bv_size_reduction_tactic.cpp]`. Purpose,
verbatim `[C: :10-15]`: *"Reduce the number of bits used to encode constants, by
using signed bounds. […] suppose `-2 <= x <= 2`, then x can be replaced by
`((sign-extend 5) k)` where k is a fresh bit-vector constant of size 3."*

Bound collection `[C: :137-204]` is a **flat scan of top-level formulas only** —
no subterm traversal, no fixpoint — matching **only `bvsle`** against a numeral:

```
(bvsle v k)        => signed_upper(v) ⊓= K
(bvsle k v)        => signed_lower(v) ⊓= K
(not (bvsle v k))  => signed_lower(v) ⊓= K+1   [drop if it wraps]
(not (bvsle k v))  => signed_upper(v) ⊓= K−1   [drop if it wraps]
```

**The entire unsigned path is `#if 0`-ed out** `[C: :115-135, :178-203]`. Width
shrinking `[C: :264-307]`, with `nb(x)` = bits needed:

```
l > u                       =>  assert false
l == u                      =>  v := numeral(l)
l<0 ∧ u<0,  i = nb(−l)      =>  v := concat(ones(w−i), fresh(i))
l<0 ∧ u≥0,  i = max(nb(−l), nb(u))+1
                            =>  v := sign_extend(w−i, fresh(i))
0 ≤ l,      i = nb(u)       =>  v := concat(zero(w−i), fresh(i))
```

Note the all-negative case is an **all-ones prefix**, not a sign-extend. There is
**no simplifier version** of this pass, and it refuses proofs and cores.

**`bv-slice`** `[C: src/ast/simplifiers/bv_slice.cpp]` — Z3's answer to §1.5.6,
and it is **weaker than Bitwuzla's**. Its own header says so `[C: bv_slice.h:11-14]`:
*"in the style of (but **not fully implementing a full slicing**) Bjorner &
Pichora, TACAS 1998 and Brutomesso et al 2008."*

- The only state is `obj_map<expr, uint_set> m_boundaries` `[C: bv_slice.h:36]` —
  per base term, a set of cut positions. **It is not a union-find.**
- Boundaries come only from top-level `(= x y)` with `bv.is_bv(x)`
  `[C: :44-55]`; `slice_eq` `[C: :57-92]` is a two-pointer alignment walk from
  the LSB end over flattened concats; `register_slice` `[C: :94-127]` first
  normalizes through nested extracts (`while is_extract(x,l,h,x): hi+=l; lo+=l`)
  then inserts cuts at `lo` and `hi+1`.
- **There is no fixpoint**: `reduce()` is literally `process_eqs(); apply_subst();`
  `[C: :32-35]`. Cuts learned from a later equality are never propagated back.
- Rebuild `[C: :183-197]`: split each term at its boundaries and re-concat. No
  model converter is needed (every rewrite is semantically the identity), and
  there are no parameters.
- **Default OFF** (`smt.bv.size_reduce` = false `[C: smt_params_helper.pyg:62]`).

`[I]` So if we implement slicing, **implement Bitwuzla's** (§1.5.6): it does the
non-overlapping partition, the exact-tiling check, and the representative
selection that Z3's explicitly does not.

**`max-bv-sharing`** `[C: src/ast/simplifiers/max_bv_sharing.cpp` +
`src/ast/rewriter/maximize_ac_sharing.cpp]`. Purpose `[C: maximize_ac_sharing.h:28-38]`:
*"rewrite AC terms to maximize sharing […] particularly useful for reducing the
number of Adders and Multipliers before bit-blasting."* Example from the header:
`(f (bvadd a (bvadd b c)) (bvadd a (bvadd b d)))` → `(f (bvadd (bvadd a b) c)
(bvadd (bvadd a b) d))`.

Operators: exactly four — `bvadd, bvmul, bvor, bvand` `[C: :167-172]`. Data
structure: a hash set of **commutativity-canonicalized binary keys**
(`entry{decl, arg1, arg2}` with the pair swapped so `arg1.id < arg2.id`
`[C: maximize_ac_sharing.h:42-66]`) — in Rust, `HashSet<(DeclId, TermId, TermId)>`
with the pair sorted, plus a scope-limit stack. Algorithm `[C: :30-103]`:

```
guards: associative, n > 2, kind ∈ {bvadd,bvmul,bvor,bvand}
if args[0] is a numeral: peel it off

Phase A (greedy reuse, RESTART the double loop after each merge):
  if 1 < n < 128:                        // MAX_NUM_ARGS_FOR_OPT
    for i<j: if cache contains (f, aᵢ, aⱼ): aᵢ = f(aᵢ,aⱼ); drop aⱼ; n--; restart

Phase B (balanced tree, INSERTING every emitted pair into the cache):
  repeat: pair up adjacent args, carrying an odd leftover up, until n == 1
```

Phase A restarts after each merge, so worst case O(n³) lookups — hence the 128
cap. No parameters, no model converter. `[I]` Why it works: each binary
`bvadd`/`bvmul` becomes a circuit at blast time; forcing two n-ary sums that
share a sub-multiset to parenthesize **identically** makes the shared sub-circuit
one hash-consed term, emitted and CNF-encoded once. **This is the same goal as
Bitwuzla's `normalize_adders` (§1.8.1) by a much simpler mechanism, and it is the
version I would implement.**

**`bv-divrem-bounds`** `[C: src/ast/simplifiers/bv_divrem_bounds.cpp]` — the
cheapest useful thing in this entire document. It is **additive, not rewriting**:
walk the ground subterms, and for each `bvudiv`/`bvurem`/`bvsdiv`/`bvsrem`/
`bvsmod` with a **symbolic** divisor, add one clause
`[C: src/ast/bv_decl_plugin.cpp:1003-1033]`, with `|x| := ite(bvsle(0,x), x, bvneg x)`:

```
bvurem(a,b)         =>  (b = 0) ∨ ¬(b   ≤u t)
bvsrem/bvsmod(a,b)  =>  (b = 0) ∨ ¬(|b| ≤u |t|)
bvudiv(a,b)         =>  (b = 0) ∨  (t   ≤u a)
bvsdiv(a,b)         =>  (b = 0) ∨  (|t| ≤u |a|)
```

Rationale `[C: bv_divrem_bounds.h:13-17]`: *"Bit-blasting a division circuit with
a symbolic divisor hides the algebraic fact that the remainder magnitude is
bounded by the divisor magnitude."* On INT_MIN `[C: :26-30]`: *"The unsigned
comparison on the absolute values keeps the bounds sound at INT_MIN […] so the
bound only ever loosens, never becomes unsound."* Everything uses `bvule`/`¬bvule`
rather than `bvult` because *"OP_ULT is not handled by
theory_bv::internalize_atom and would trigger UNREACHABLE"* `[C: bv_decl_plugin.cpp:1012-1014]`.
The lemmas are valid, so **no model converter is needed and `supports_proofs()`
is true** `[C: bv_divrem_bounds.h:56]`. It is in the QF_BV preamble, always on.

**`bv-bounds`** — three implementations over `mod_interval`
`[C: src/math/interval/mod_interval.h:22-28]`, a *modular closed* interval with a
`tight` flag (needed for sound negation: `!tight ⇒ negate gives full`) and two
instantiations (`uint64_t` fast path, `rational` above 64 bits). Atom extraction
`[C: src/ast/rewriter/bv_bounds_base.h:55-114]` matches `bvule`/`bvsle` against a
numeral, plus `(= 0 x[sz-1:lo])` ⇒ `[0, 2^lo − 1]` **not tight**. Nothing matches
`bvult`/`bvslt`; the header states the precondition. The one genuinely
size-reducing rule is `zero_patch` `[C: :169-210]`:

```
t = f(.., arg, ..), arg not an extract, bound(arg) = [lo,hi], nb = nb(hi), 0 < nb < w
  =>  arg := concat(zero(w − nb), extract(nb−1, 0, arg))
```

**and the interval-tightening branch is dead code** — verified myself, the guard
is literally `else if (false && intr != b)` `[C: :271]`. So a constraint is only
ever proved true, proved false, or turned into an equality.

**`elim-small-bv`** `[C: src/tactic/bv/elim_small_bv_tactic.cpp]` — finite
expansion of *quantified* small BV variables; `max_bits` default **4**, plus a
hard `if (bv_sz >= 31) return false`. **We have the analogous
`expand_quantifiers`** in `crates/axeyum-rewrite/src/quantifiers.rs` with
`QUANT_EXPAND_BIT_LIMIT` and a cumulative instance cap — arguably better guarded.

**`bvarray2uf`** `[C: src/tactic/bv/bvarray2uf_rewriter.cpp]` —
Wintersteiger–Hamadi–de Moura array elimination, replacing each BV-array by a
fresh unary UF and emitting quantified defining axioms for `=`, `ite`, `select`,
`const`, `map`, `store`. Anything outside the fragment **throws**
`default_exception("not handled by bvarray2uf")` `[C: :196-198]`, so it must be
probe-guarded. `[I]` Different mechanism from our `eliminate_arrays`
(read-over-write + Ackermann); not obviously better for us, and it introduces
quantifiers.

**`dt2bv`** `[C: src/tactic/bv/dt2bv_tactic.cpp]` — enum datatypes → BV. The
tactic is only a sort-eligibility analysis; `enum2bv_rewriter` does the work
(constructor index → numeral, plus a domain constraint `bvule(x, n−1)` unless `n`
is a power of two).

### 2.10 `bv_rewriter`: the structural rules worth taking

`[C: src/ast/rewriter/bv_rewriter.cpp]`, 3452 lines. Only the structural ones.

**`mk_extract`** `[C: :766-921]` — the most productive function in the file:

```
low==0 ∧ high==sz−1                =>  arg
numeral                            =>  fold
x[h2:l2][high:low]                 =>  x[high+l2 : low+l2]
(extract (concat a₁..aₙ))          =>  walk from LSB; if the window lies inside one
                                       aᵢ return it (or an extract of it), else emit a
                                       concat of boundary extracts + whole middle args
(op a₁..aₙ)[high:low]              =>  (op a₁[high:low] .. aₙ[high:low])
                                       for op ∈ {bvnot,bvor,bvxor}  — unrestricted
                                       for op ∈ {bvadd,bvmul}       — ONLY when low == 0
(ite c t e)[h:l]                   =>  (ite c t[h:l] e[h:l])
                                       [ref_count(t)==1 ∨ ref_count(e)==1 ∨ ¬is_ite(t) ∨ ¬is_ite(e)]
(bvashr t k)[high:0]               =>  t[high+k : k]        [k numeral, high < sz−k]
```

**The `low == 0` restriction on `bvadd`/`bvmul` is the carry-independence
condition** — only the *low* bits of a sum or product are a function of the low
bits of the operands. This is the same rule as Bitwuzla's `BV_EXTRACT_ADD_MUL`
(§3.1) with the same guard, found independently. The `ref_count` guard on the ite
rule cites Z3 issue #2359 `[C: :898-901]` — it is a **sharing guard**, the same
idea as the CNF encoder's.

**`mk_concat`** `[C: :1712-1787]` — one left-to-right pass:

```
concat(.., C1, C2, ..)              =>  concat(.., C1·2^sz2 + C2, ..)
concat(.., (concat a..b), ..)       =>  flatten
concat(.., x[h1:l1], x[h2:l2], ..)  =>  concat(.., x[h1:l2], ..)   [l1 == h2+1]
concat(t,..,t), t = (ite c a b)     =>  (ite c (concat a..a) (concat b..b))
```

**Extensions are eliminated entirely** `[C: :1835-1886]`:
`zero_extend(n,a) => concat(0^n, a)`, `sign_extend(n,a) => concat(a[sz−1:sz−1]×n, a)`,
`repeat(n,a) => concat(a × n)`. So downstream passes only ever see `concat` and
`extract` — a real simplification for a reimplementation. The inverse direction
exists for bitwise ops `[C: :1815-1833]`:
`op(concat(0^p,x₁),…) => zero_extend(p, op(x₁..xₙ))`.

**`bvand` is not implemented** — it is De Morgan'd into `bvor`
`[C: :2332-2342]`, so `bvor` `[C: :1888-2061]` is the one real implementation.

**Two rules that directly reduce blasting cost:**

```
-- disjoint bitfields: if bit-position-wise at most ONE argument can be non-zero
bvadd(t₁..tₙ)  =>  bvor(t₁..tₙ)                     [C: :2480-2570]
   -- removes the entire carry chain.

-- isolate, with the reason stated in source [C: :3101-3102]:
-- "Try to rewrite t1 + t2 = c --> t1 = c - t2. Reason: it is much cheaper to bit-blast."
(= C (bvadd t₁ t₂ .. tₙ))  =>  (= t₁ (bvsub C (bvadd t₂..tₙ)))     [C: :2865-2884]
```

**`mk_eq_concat`** `[C: :2761-2834]` is the concat-vs-concat splitter — a
two-pointer LSB walk emitting one equality per aligned fragment. It carries a
warning we should heed `[C: :2837-2843]`:

> splitting `(= x (concat ...))` into per-slice extract equalities rewrites an
> eliminable `(= VAR t)` equality into `(= (extract .. VAR) t)` fragments that
> destructive equality resolution (der) can no longer use to eliminate the bound
> variable.

**i.e. concat splitting can *destroy* a solved form.** Bitwuzla's version guards
against this differently (only fire when all four extracts vanish or bottom out
on a symbol, §1.5.4). Either guard is needed; the naive rule is a regression.

**`mk_bv_add`/`mk_bv_mul` normal form** goes through
`poly_rewriter::mk_nflat_add_core` `[C: src/ast/rewriter/poly_rewriter_def.h:530-670]`:
flatten, one pass computing the numeral sum and detecting repeated power
products, an "expensive case" `[C: :572]` collecting coefficients per distinct
power product, then sort by `mon_lt`. The ordering key `[C: :506-525]` is **the
AST id of the power product** — deterministic (ids are creation order) but not
semantically meaningful. `get_power_product(t)` `[C: :432-435]` is what makes
`3x + 5x` collapse to `8x`.

`[I]` **We have AC flatten + sort by `TermId` + constant folding
(`canonical.rs:1409-1460`) but no coefficient collection.** Adding
`get_power_product`-style grouping is a small, well-specified change.

### 2.11 Cost and gating

`[C]` **No source comment in any of these files calls a pass "expensive"** — a
grep for `expensive|too slow|blowup|exponential` over `tactic/bv/`,
`ast/simplifiers/bv*`, and `maximize_ac_sharing.*` returns nothing. The cost
signals are structural:

- `MAX_NUM_ARGS_FOR_OPT 128` bounding the O(n³) restart search in
  `maximize_ac_sharing` `[C: :52,57]`.
- `bv_ineq_consistency_test_max` **default 0**, which disables `bv_bound_chk`
  entirely out of the box `[C: src/params/rewriter_params.pyg:9]`.
- `bv_sz >= 31` and `max_bits = 4` in `elim_small_bv`.
- `eliminate_predicates`' three DP blow-up thresholds `[C: :663-668]`.
- `elim_unconstrained`'s `return` at `num_parents > 1` and its 3-round cap.
- `ctx_simplify_tactic`'s `may_simplify` pre-filter with the comment *"skip
  common case: single bound constraint without any context for simplification"*.

**Always on in the QF_BV path:** `simplify` (three times, different params),
`propagate-values`, `solve-eqs`, `elim-uncnstr`, `bv-divrem-bounds`,
`max-bv-sharing`. Everything else is proof-gated, core-gated, parameter-gated, or
probe-gated. **Proof/core-gated** (i.e. satisfiability-preserving only):
`reduce-bv-size` and `ackermannize_bv` `[C: qfbv_tactic.cpp:68,79]`; in the
simplifier framework the same role is played by `supports_proofs()`, which is
**false** for `elim_unconstrained`, `solve_eqs`, `propagate_values`,
`bound_simplifier`, `injectivity`, `bvarray2uf`, `bv::slice`.

Selected defaults: `smt.elim_unconstrained` **true**; `smt.solve_eqs` **true**,
`.linear` **false**; `propagate_values.max_rounds` **4**;
`smt.bound_simplifier` **true**; `smt.bv.size_reduce` (i.e. `bv-slice`)
**false**; `propagate_eq` **false**; `ctx-simplify max_depth` **1024**;
`bv_le2extract`, `elim_sign_ext`, `bit2bool`, `hi_div0`, `bv_sort_ac` **true**;
`split_concat_eq`, `blast_eq_value`, `mul2concat`, `bv_extract_prop`,
`bv_not_simpl`, `bv_ite2id`, `bv_le_extra` **false**.

### 2.12 General passes that pay across theories

One paragraph each; these are the cross-division items.

- **`eliminate_predicates`** `[C: src/ast/simplifiers/eliminate_predicates.cpp]`
  — clausify, mine binary clauses `{p(x̄), ℓ}` / `{¬p(x̄), ℓ}` for **macro
  definitions** `p(x̄) := ℓ`, then bounded DP resolution (skip when
  `pos≥4 ∧ neg≥2`, etc. `[C: :663-668]`). Model update is `p := ⋁ residue(pos)`
  or `p := ⋀ ¬residue(neg)`, whichever is smaller. **Helps UF/UFLIA/UFBV** with
  Boogie/Dafny-style macro axioms; useless for pure QF_BV.
- **`euf_completion`** — a real E-graph with E-matching, doing **equality
  saturation** and then rewriting every assertion to its class representative,
  ≤ 4 rounds `[C: :227-241]`. Representative selection is `is_gt` `[C: :1254-1297]`:
  values first, then depth, then term count, then decl id. **Not in the default
  pipeline.** Helps heavy-UF and ground-defining-equation problems.
- **`demodulator_simplifier`** — Knuth–Bendix-style interreduction over
  *orientable unit equations*, with forward and backward decl indexes
  `[C: demodulator_simplifier.h:20-37]` and a saturation loop that reschedules
  processed formulas when a new demodulator appears. Helps quantified logics
  where the input states function *definitions*.
- **`reduce_args_simplifier`** — Ackermann-like monomorphisation: if argument
  position `i` of `f` is always a value, specialize `f` per combination. Model
  side is `f(x̄) := ite(…, f_key1(..), ite(…))`, pushed as **one loose entry**
  `[C: :379]` because the transform is only satisfiability preserving. Helps
  QF_UF / QF_AUFBV / QF_UFBV with array/heap and map encodings.
- **`injectivity_simplifier`** — header-only. Recognize exactly
  `(forall ((x S)) (= (g (f x)) x))`, record `f` injective (**without removing
  the axiom**), then `(= (f a) (f b)) => (= a b)`. The map persists across
  `reduce()` calls, which is right for incremental use. It removes an entire
  class of E-matching triggers.
- **`bound_simplifier`** (registered `propagate-ineqs`) — interval propagation
  over arithmetic, ≤ 5 rounds. The payoff rule is **`mod` elimination**
  `[C: :58-97]`: with `[lo,hi] = bounds(x)`, `N > hi ∧ lo ≥ 0 ⇒ (mod x N) = x`,
  and `2N > hi ∧ lo ≥ N ⇒ (mod x N) = x − N`. **Helps LIA/LRA/NIA and every
  integer encoding with `mod`/`div`** — which includes our own int-blast ladder
  and BV-to-int translations.
- **`ctx_simplify_tactic`** — contextual simplification by nesting: inside an
  `or`, assert each simplified sibling **negated** as context for the rest;
  inside an `and`, positive; for an `ite`, assert `c` for the then-branch. Two
  sweeps (forward then backward), popping between. The cache is **keyed on expr
  id and versioned by scope level** — an entry computed under different
  assumptions is invisible `[C: :308-321]`. Knobs: `max_depth` **1024**,
  `bail_on_blowup` false.
- **`dominator_simplifier`** — the same idea via Cooper/Harvey/Kennedy iterative
  dominators over the expression DAG, with edges **from subterm to parent**, so
  dominance answers "does every path from this subterm to the root go through
  X". The payoff over `ctx_simplify` is that a subterm *dominated by* the
  then-branch can be simplified under `c` even though it is shared syntactically
  elsewhere in the DAG.

`[I]` For our 12 divisions, `bound_simplifier`'s `mod` elimination and
`ctx_simplify`'s or/and context are the two with the widest reach.

### 2.13 Three defects found in Z3 while reading — do not inherit them

Each verified directly, not taken on report:

1. **`solve_eqs_max_occs` is dead.** `collect_num_occs` is never called
   (`grep -rn collect_num_occs src/` returns only declarations, definitions, and
   the internal call between the two overloads), so the QF_BV preamble's
   "conservative gaussian elimination" cap does nothing.
2. **`bv_bounds`' interval-tightening branch is disabled**: the guard is
   literally `else if (false && intr != b)` `[C: src/ast/rewriter/bv_bounds_base.h:271]`.
3. **A parameter key mismatch**: both bv-bounds drivers read the key
   `propagate_eq` while advertising `propagate-eq`.


---

## 3. The transformations as rewrite rules

Everything below is transcribed from source with a `file:line`. Notation:
`x` = a free symbol (SMT-LIB "constant"), `c`/`v` = a bit-vector value,
`a`,`b`,`t`,`s` = arbitrary terms, `w` = bit width, `fresh_[n]` = a newly
declared symbol of width `n`.

### 3.1 Structural normalization (denotation-preserving, always safe)

```
-- Extract pushed through the whole add/mul sub-DAG.  Requires lo = 0.
   [C: references/bitwuzla/src/rewrite/rewrites_bv.cpp:1757-1808, BV_EXTRACT_ADD_MUL]
((_ extract u 0) E)   where E is built only from bvadd / bvmul / bvnot
  =>  E' , where E' is E rebuilt bottom-up with the same operators over
           ((_ extract u 0) leaf) at every leaf.
-- This is the single biggest width reducer in the catalogue: it turns a
-- w-bit multiplier whose top bits are discarded into a (u+1)-bit multiplier,
-- which is quadratically cheaper to bit-blast.

-- Extract of a concat, both the fully-inside and the straddling cases.
   [C: BV_EXTRACT_CONCAT_FULL_LHS / _FULL_RHS / _LHS_RHS / BV_EXTRACT_CONCAT]
   We already have these: crates/axeyum-rewrite/src/canonical.rs
   (bv.extract_concat.v1, bv.extract_concat_straddle.v1).

-- Concat of bvnots hoists the negation out.
   [C: references/bitwuzla/src/rewrite/rewrites_bv_norm.cpp:61-72, NORM_BV_CONCAT_BV_NOT]
(concat (bvnot a) (bvnot b))   =>  (bvnot (concat a b))

-- Disjoint-field addition IS concatenation.
   [C: rewrites_bv_norm.cpp:115-130, NORM_BV_ADD_CONCAT]
(bvadd (concat (_ bv0 M) a) (concat b (_ bv0 M)))  =>  (concat b a)
(bvadd (concat a (_ bv0 M)) (concat (_ bv0 M) b))  =>  (concat a b)
-- Replaces a w-bit ripple-carry adder with zero gates.
```

### 3.2 Factoring (reduces the *number* of expensive gadgets — gate behind the cost oracle)

```
   [C: rewrites_bv_norm.cpp:275-328, NORM_FACT_BV_ADD_MUL]
(bvadd (bvmul a t1) (bvmul a t2))   =>  (bvmul a (bvadd t1 t2))     -- 2 multipliers -> 1
(bvadd a (bvmul a t2))              =>  (bvmul a (bvadd 1 t2))      -- a not a value
   [C: rewrites_bv_norm.cpp:342, 388, 408 — NORM_FACT_BV_ADD_SHL / _SHL_MUL / _MUL_SHL]
(bvadd (bvshl a t1) (bvshl a t2))   =>  (bvmul a (bvadd (bvshl 1 t1) (bvshl 1 t2)))
(bvadd (bvshl a t1) a)              =>  (bvmul a (bvadd (bvshl 1 t1) 1))
```

`[I]` The `shl -> mul` direction is a *deliberate cost inversion*: it trades two
barrel shifters for one multiplier. That is only a win sometimes, which is
exactly why Bitwuzla runs these inside the AIG-scored `normalize` pass (§1.8)
rather than in the unconditional rewriter.

### 3.3 Solved forms (equisatisfiable; each needs one `trail.define`)

```
-- Base case (we have this).
(= x t) , x not free in t          =>  x := t,  assertion dropped
p       , p a Boolean symbol       =>  p := true
(not p) , p a Boolean symbol       =>  p := false

-- Gaussian elimination over Z/2^w  [C: variable_substitution.cpp:37-189]
-- decompose(e) -> (factor, x, rest)  with factor ODD, bound 100 recursive steps:
--   (bvnot e)      : (f,x,r) |-> (-f, x, (bvnot r))
--   (bvadd e0 e1)  : e_i |-> (f,x,r)  gives (f, x, (bvadd e_{1-i} r))
--   (bvmul c e)    : c a value with LSB=1  gives (c*f, x, (bvmul c r))
--   x              : (1, x, 0)
(= lhs rhs) , decompose(lhs) = (f, x, r)
  =>  x := (bvmul (bvsub rhs r) (modinv f))       -- modinv f exists since f is odd

-- Concat splitting  [C: variable_substitution.cpp:370-404]
(= (concat a_[n] b) c_[m])
  =>  (and (= ((_ extract m-1  m-n) (concat a b)) ((_ extract m-1  m-n) c))
           (= ((_ extract m-n-1 0) (concat a b)) ((_ extract m-n-1 0) c)))
  [guard: fire only if all four extracts either vanish or bottom out on a symbol]
  then push each resulting conjunct as its own top-level assertion.

-- Bound-derived width reduction (Bitwuzla default OFF)
   [C: variable_substitution.cpp:205-321]
(bvult x c) / (bvule x c),  clz = clz(c),  0 < clz < w
  =>  x := (concat (_ bv0 clz) fresh_[w-clz])
(bvugt x c) / (bvuge x c),  clo = clo(c),  0 < clo < w
  =>  x := (concat (_ ones clo) fresh_[w-clo])
(bvslt x c) / (bvsle x c),  msb(c)=1, clz = clz(c[w-2:0]), clz < w-1
  =>  x := (concat (min_signed_[clz+1]) fresh_[w-clz-1])
(bvsgt x c) / (bvsge x c),  msb(c)=0, clo = clo(c[w-2:0]), clo < w-1
  =>  x := (concat (max_signed_[clo+1]) fresh_[w-clo-1])
  [c may be given as (bvnot v) for a value v; flip the relation if x is on the right]

-- Variable slicing / extract elimination  [C: variable_substitution.cpp:542-1300]
   Given assertions  (= ((_ extract u_i l_i) x) t_i)  for i = 1..k :
   1. boundaries = sort_unique( { l_i } union { u_i + 1 } )
   2. sub-ranges = consecutive boundary pairs [b_{j+1}-1 : b_j]
   3. for each sub-range, terms = every t_i whose [u_i:l_i] covers it, re-extracted
      (composing nested extracts, never stacking them)
   4. require the sub-ranges to tile [w-1:0] exactly, else abandon
   5. per sub-range pick one representative, preferring value > symbol > other,
      tie-break on node id; skip x itself and extracts of x
   6. if every sub-range got one:  x := (concat rep_hi ... rep_lo)
      (occurs-check the concat first)

-- Embedded constraints  [C: embedded_constraints.cpp:52-96]
   For every top-level assertion A (or (not A)):  A := true  (resp. false),
   applied to the CHILDREN of every assertion, not to the assertion itself.

-- Top-level AND flattening  [C: flatten_and.cpp:30-67]
   assertion_i = (and ...)  =>  replace with `true`, push every leaf of the
   maximal AND-spine (visited-set deduplicated) as its own assertion.
```

### 3.4 The BV div/rem encoding (Bitwuzla's version, currently disabled there)

```
   [C: elim_udiv.cpp:81-117]
(bvudiv a b) => q ,  (bvurem a b) => r ,  q,r fresh, keyed on the (a,b) pair
  and add:
    (=> (distinct b 0) (= (bvadd (bvmul q b) r) a))
    (=> (distinct b 0) (bvult r b))
    (=> (= b 0)        (= q ones))
    (=> (= b 0)        (= r a))
    (not (bvumulo q b))
    (not (bvuaddo (bvmul q b) r))
```

### 3.5 AIG-level local minimization

See the full four-level table in §1.9. The two rules we lack that carry the
compounding are:

```
Substitution (asym):  ~(a /\ b) /\ c   with b = c   ==>  rewrite to  ~a /\ c , RE-RUN
Substitution (sym):   ~(a /\ b) /\ (c /\ d)  with b in {c,d}  ==>  ~a /\ (c /\ d) , RE-RUN
```

`[C: references/bitwuzla/src/lib/bitblast/aig/aig_manager.cpp:306-374]`. The
`continue` that re-enters the `do { ... } while(true)` loop is the whole point:
each substitution exposes a new shape for the level-1 and level-2 rules.


---

## 4. What Axeyum already has, and what is genuinely missing

Read directly from `crates/`, 2026-09-08. **Do not treat any "missing" row as
proven absent by name search alone** — each was checked by looking for the
*step*, not the identifier, and the file:line is given so the next lane can
re-check.

### 4.1 Existing passes

| Bitwuzla / Z3 pass | Ours | Where | Gap |
|---|---|---|---|
| `rewrite` (canonicalizer) | **yes** | `crates/axeyum-rewrite/src/canonical.rs` (5,290 lines, 60 named rule ids — one of which, `control.denotation_violation.v1`, is a deliberate negative control with a manifest carrying preservation class + projection obligation + test route) | ~60 rule ids vs Bitwuzla's 296 rule kinds; no rule *levels* |
| `variable_substitution` — base case `(= x t)` | **yes** | `solve_eqs.rs` (415 lines), occurs check + reverse-replay trail, fuel-bounded at 5M node visits | no linear/Gaussian form, no concat splitting, no ineq-derived form, no slicing |
| constant propagation | **yes** | `propagate_values.rs` (538 lines), fixpoint, batched DAG rebuild per round | only *syntactic* top-level `x = c` (its own doc, lines 20-23) |
| `elim_unconstrained` | **partial** | `elim_unconstrained.rs` (688 lines) | only `bvnot`, `bvneg`, `bvadd`, `bvxor`, `bvsub`, `bvmul`-by-odd-constant (`invertible`, `:154-158`). No Boolean, ITE, comparison, concat/extract, array or arithmetic rules |
| Ackermannization | **yes** | `functions.rs` (1,225 lines), eager, ADR-0013 |  |
| array elimination (read-over-write) | **yes** | `arrays.rs` (1,076 lines), ADR-0010 |  |
| int div/mod elimination | **yes** | `int_divmod.rs` (842 lines) | Bitwuzla's BV analogue is disabled anyway |
| int blasting | **yes** | `int_blast.rs` (634 lines), ADR-1702 |  |
| quantifier alpha-normalization | **yes** | `alpha.rs` (942 lines) — matches Bitwuzla `PassQuant::alpha_normalize` |  |
| quantifier expansion/instantiation | **yes** | `quantifiers.rs`, `crates/axeyum-solver/src/quant_skolemize.rs` (NNF + Skolemization + prenexing) |  |
| datatype simplification | **yes** | `datatypes.rs` (147 lines) |  |
| model reconstruction trail | **yes** | `reconstruct.rs` (187 lines) — reverse replay, exactly Z3's `model_reconstruction_trail` role |  |
| per-pass term-size stats | **yes, opt-in** | `pass_stats.rs` (291 lines) — `_with_stats` wrappers, `PassSize{dag_nodes, tree_nodes, max_depth}` | not wired into the driver; no timers |
| AIG structural hashing | **yes** | `crates/axeyum-aig/src/lib.rs` | see 4.3 |
| AIG→CNF with ITE/XOR/AND-tree extraction | **yes, ahead of Bitwuzla** | `crates/axeyum-cnf/src/lib.rs:3718` (`encode_xor_gate`), `:3751` (`encode_not_ite_gate`), `:3822` (`encode_not_and_reverse`), `:3887` (`encode_and_tree_gate`) | none — Bitwuzla has TODOs where we have code |
| CEGAR abstraction of heavy BV ops | **yes, but blunt and off** | `crates/axeyum-solver/src/lazy_bv.rs` | refines with the exact `fresh == op(a,b)` only; `SolverConfig::lazy_bv` defaults **false** (`backend.rs:224-232`) |

### 4.2 Genuinely absent (searched for the step, not the name)

| Missing | Evidence of absence | Section above |
|---|---|---|
| **A pass abstraction at all.** There is no `trait Pass`. The pipeline is a hard-coded call sequence, written out **twice**, with **different semantics**: `crates/axeyum-solver/src/preprocess.rs:78-134` iterates `MAX_PREPROCESS_ROUNDS = 8` (`:32`); `crates/axeyum-solver/src/auto.rs:1933-1975` (`preprocess_reduce`) runs the same four passes **exactly once**, no fixpoint. | read both | §1.2 |
| **Flatten top-level `and` into separate assertions.** `flatten_binary_spine` exists in `crates/axeyum-solver/src/term_walk.rs` but is used by array-scenario detectors (`array_binary_search.rs:375`, `array_fifo.rs:974`, `array_memcpy.rs:247`, `array_sort2.rs:542`), not by the preprocessing driver. `grep -n flatten crates/axeyum-solver/src/preprocess.rs crates/axeyum-rewrite/src/*.rs` → nothing. | | §1.4 |
| **Gaussian elimination over BV** (`factor*x + rest = t` with odd `factor`) | `solve_eqs.rs` doc lines 3-9 state the scope is a bare variable on one side | §1.5.2 |
| **Concat splitting of equalities** into two independent equalities | not in the 60 canonical rule ids; `EQUAL_BV_CONCAT`'s analogue is absent | §1.5.4 |
| **Variable slicing / extract elimination** (boundary sweep, partition, rebuild as concat) | `grep -ni "non.overlap\|boundar" crates/axeyum-rewrite/src crates/axeyum-bv/src` → nothing relevant | §1.5.6 |
| **Extract pushed through `bvadd`/`bvmul`** — `rewrite_extract` (`canonical.rs:2430-2497`) handles whole/nested/concat/extend/bitwise/ite and stops. Bitwuzla's `BV_EXTRACT_ADD_MUL` is a whole-sub-DAG rewrite. | read the dispatch | §3 |
| **Embedded-constraint substitution** (top-level `A` ⇒ `A:=true` inside other assertions) | `grep -rni "context.*simplif\|dominator" crates/axeyum-rewrite crates/axeyum-solver` → one unrelated hit | §1.7 |
| **Skeleton preprocessing** (SAT-simplify the Boolean abstraction, lift fixed literals back to word level) | no such pass | §1.6 |
| **Cost-model-gated normalization** — *partly present, do not treat as absent.* We already gate the **whole preprocessing reduction** on lowered AIG size: `reduction_shrinks_encoding` (`crates/axeyum-solver/src/auto.rs:1975-2010`) lowers both the original and the reduced query and declines the reduction when the AIG grew, with three measured benchmarks in its doc comment (`062-bench_2195`: term DAG 1375 → **1215** while the AIG grew 35 329 → 51 724). What is missing is (a) the **budgeted, interleaved race** form — ours lowers both sides fully, Bitwuzla advances candidates in 100 000-gate slices and stops early (`normalize.cpp:1322-1346`) — and (b) applying it **per pass / per candidate rewrite** rather than once for the whole pipeline. | read the function; already recorded in the sibling survey (see §0.1) | §1.8 |
| **Bounds-driven width reduction** | `grep -ni "reduce.*width\|shrink.*width\|narrow"` over `axeyum-rewrite` → only test-local identifiers | §1.5.3 |
| **Top-level term-ITE elimination** | `grep -rni "term ite\|elim_term_ite\|ite lifting"` over both crates → nothing | Z3 `elim_term_ite` |
| **BV-generalized destructive equality resolution.** Plain DER is *already* flagged as absent by `pipeline-survey-2026-09/term-rewriting-infrastructure.md` §0.7 / §3 (it cites Z3's `der.cpp`). What is new here is Bitwuzla's generalization: any equality in the body mentioning the bound variable from which an **unconditional** inverse can be computed, not only the syntactic `(= x t)` shape. | read `quant.cpp:315-374`; DER absence already established elsewhere | §5.2b |
| **A shared BV inverter.** Inverses exist only as `elim_unconstrained.rs::invert` / `invertible` (`:154-200`), private, unconditional, six operators. Bitwuzla's serves three consumers and covers 21. | read the module | §5.2b |
| **Cached structural predicates on interned nodes.** `has_quantifier` (`crates/axeyum-solver/src/auto.rs:1078-1092`) answers by full DAG walk with a `BTreeSet`; Bitwuzla reads a bit (`node.h:41-53`). | read both | §5.6 |
| **`bv-divrem-bounds`** — for each `bvudiv`/`bvurem`/`bvsdiv`/`bvsrem`/`bvsmod` with a **symbolic** divisor, add one bounding clause (`(b=0) ∨ ¬(b ≤u t)` etc.). Additive, valid (no model converter), proof-supporting, always on in Z3's QF_BV preamble. | `grep -rni "divrem\|umulo\|uaddo"` over `crates/axeyum-rewrite/src` → nothing | §2.9 |
| **`max_bv_sharing`** — reassociate n-ary `bvadd`/`bvmul`/`bvor`/`bvand` so chains sharing a sub-multiset parenthesize identically, making the shared adder/multiplier one hash-consed term. We AC-flatten and sort by `TermId` (`canonical.rs:1409-1460`), which is a *canonical* order, not a *sharing-maximizing* one — two chains with different membership get different trees. | read our AC path | §2.9 |
| **Disjoint-bitfield addition**: `bvadd(t₁..tₙ) => bvor(t₁..tₙ)` when, bit position by bit position, at most one argument can be non-zero. Removes the entire carry chain. | not in the 60 rule ids; `rewrite_bv_add` (`canonical.rs:1472`) has no bit-position analysis | §2.10 |
| **`isolate_term`**: `(= C (bvadd t₁ .. tₙ)) => (= t₁ (bvsub C (bvadd t₂..tₙ)))`. Z3 states the reason in source: *"it is much cheaper to bit-blast"*. We have `bv.eq_add_constant_cancel.v1`, which is narrower (cancels a shared constant, does not isolate a term). | read the rule id list and `rewrite_bv_add` | §2.10 |
| **Coefficient collection in AC normalization** (`3x + 5x → 8x` via a power-product key). We flatten, sort and fold *constants*, but do not group repeated non-constant operands. | `canonical.rs:1409-1460` | §2.10 |
| **A backward sweep in `propagate_values`.** Z3 runs forward **then backward** per round, rebuilding the substitution between directions; ours is forward-only. | `propagate_values.rs` doc lines 1-10 vs `[C: propagate_values.cpp:67-104]` | §2.8 |
| **Loose vs rigid model-trail entries.** `ModelReconstructionTrail` has one entry kind (`Define`, `reconstruct.rs:29-33`). Z3 distinguishes satisfiability-preserving (loose — roll back and resurrect the original formulas if the symbol becomes constrained again) from equivalence-preserving (rigid — push the substitution forward). Correct today because our pipeline is one-shot; mandatory before it can be incremental. | read both | §2.5 |
| **Shared occurrence/parent index in the IR.** `Occurrences{refs, parent}` is **private** to `elim_unconstrained.rs:82-115` and is **recomputed over the entire assertion forest after every single elimination** (`:344-360`), i.e. `O(eliminations × DAG)`. | read the loop | §5.2 |

### 4.3 AIG local minimization: exactly which rules we are missing

`crates/axeyum-aig/src/lib.rs` has:

- **Level 1, complete**: `simplify_and` (`:732-744`) covers boundedness,
  contradiction, neutrality, idempotence.
- **Level 2, partial**: `absorb_or_rhs` (`:389-401`) gives *subsumption
  (asymmetric)* and one absorption case; `simplify_and_by_or_consensus` +
  `consensus_shared_operand` (`:403-407`, `:745-755`) gives the *resolution* rule.
- **Level 3 and 4: absent.** `and()` (`:345-381`) tries `simplify_and`, then
  `simplify_and_by_absorption`, then the structural-hash table, then allocates —
  there is no generic *rewrite-the-operands-and-re-run* structure. (Two branches
  of `absorb_or_rhs` do call `self.and(...)` again, `:394-399`, so a narrow
  re-entry exists; the level-3/4 substitution and idempotence rules, which are
  the general form of that, do not.)

So relative to §1.9's table, we are missing: contradiction (asym+sym),
subsumption (sym), idempotence (asym at level 2 and sym at level 4), and **both
substitution rules with the re-entry loop**. `[I]` The substitution rules are the
ones that matter most, because they are the only ones that *rewrite the operands
and re-run the whole rule set*, which is where the compounding comes from.


---

## 5. Architecture: what a reusable pass layer needs

This section is the design brief. The point is **not** to add nine more
functions to `axeyum-rewrite`; it is that we currently have no place to put a
tenth, and two divergent hard-coded copies of the ninth.

### 5.1 The pass contract

Both reference solvers converge on the same shape, and ours should too:

```rust
/// One word-level preprocessing pass.
pub trait Pass {
    /// Stable id, used in logs, stats keys, and config.
    fn id(&self) -> &'static str;

    /// Transform the assertion set in place. Progress is signalled through
    /// `ctx`, never by a return value.
    fn apply(&mut self, ctx: &mut PassCtx<'_>) -> Result<(), PassError>;

    /// Optional single-term form, for pushing a lemma or a new assertion
    /// through an already-established substitution state.
    fn process(&mut self, ctx: &mut PassCtx<'_>, t: TermId) -> Result<TermId, PassError> {
        let _ = ctx; Ok(t)
    }
}
```

`[C]` mirrors `PreprocessingPass` (`references/bitwuzla/src/preprocess/preprocessing_pass.h:34-122`).
The `process` default matters: Bitwuzla uses it for the shorter lemma-path
pipeline (`preprocessor.cpp:147-158`), and we will need it the moment
preprocessing meets `check-sat-assuming` or a CEGAR refinement round.

### 5.2 What the context must carry

The passes above need exactly six shared services. Five we already have in some
form; the assertion vector and the occurrence index are the new work.

1. **`AssertionVector`** — an ordered, mutable view over the current assertion
   list with `replace(i, t)`, `push_back(t, parent)`, `modified()`,
   `num_simplified()`, `is_inconsistent()`. The `modified` flag lives here, not
   on the pass, because a pass may make progress through several mechanisms.
   `parent` is the provenance edge; even before we ship unsat cores it is what
   makes a pass debuggable. **New.**
   `[C: references/bitwuzla/src/preprocess/assertion_vector.h:28-96]`

2. **An occurrence index** — `refs: Map<TermId, usize>` plus
   `parent: Map<TermId, (TermId, slot)>` over the assertion forest, with roots
   counted (a term that is also a top-level assertion must never look
   single-use). We already compute exactly this in
   `crates/axeyum-rewrite/src/elim_unconstrained.rs:82-115`, but privately and
   **from scratch after every single elimination** (`:344-360`). Lift it to a
   shared, *incrementally maintained* structure: when a node is replaced,
   decrement its children's counts and push any that fell to one onto a
   worklist. That converts unconstrained elimination from
   `O(eliminations × DAG)` to `O(DAG)` and is the same worklist Z3 uses.
   **Lift + make incremental.**

   Prior art in-tree: `crates/axeyum-cnf/src/lib.rs` already builds exactly this
   at the AIG level — `node_use_counts` (`:3483`) feeding the gate planners
   (`:3519-3545`), which refuse to extract an XOR/ITE gate whose helper nodes are
   shared. Copy the shape, not the code.

3. **A substitution map + shared substitute-with-cache.** We have
   `replace_subterms` (`canonical.rs`, re-exported at `lib.rs:52`), used by
   `solve_eqs`, `propagate_values`, `elim_unconstrained` and `lazy_bv`. What is
   missing is a **persistent, invalidated-on-change** cache owned by the context,
   rather than a fresh `HashMap` per call site. Bitwuzla clears its cache only
   when the substitution map actually grows
   (`variable_substitution.cpp:747-751`). **Exists; needs to move into the ctx.**

4. **`ModelReconstructionTrail`** — we already have the right thing
   (`crates/axeyum-rewrite/src/reconstruct.rs`), with the reverse-replay
   discipline documented at lines 18-24. The context should own **one** trail
   that passes append to, instead of each pass returning its own for the driver
   to `append`. That removes a whole class of ordering bug from the call sites.
   **Exists; needs to move into the ctx.**

5. **A cost oracle.** `Cost::aig_ands(&[TermId]) -> u64`, computed by a partial,
   **interruptible** AIG bit-blast: abstract every operator you do not model as a
   fresh AIG constant, advance in fixed gate-count slices, and stop as soon as
   one candidate is provably cheaper than another.
   `[C: references/bitwuzla/src/preprocess/pass/normalize.cpp:48-102, :1320-1362]`.
   We have the AIG (`crates/axeyum-aig`) and the lowering (`crates/axeyum-bv`),
   so this is a wrapper, not a new subsystem. Note Bitwuzla's guard: **disable
   scoring entirely above 64-bit operands** (`normalize.cpp:1398-1403`).
   **New, and cheap for us.**

6. **Per-pass statistics: a timer and a counter set, keyed by pass id.**
   `pass_stats.rs` already computes the before/after `PassSize`; it is opt-in via
   separate `_with_stats` functions and nothing in the driver calls them. The
   driver should always record `(pass_id, elapsed, size_before, size_after,
   n_eliminated)` — **this is the ablation data we do not currently have and
   cannot get any other way.** **Exists; needs wiring.**

### 5.2b The one component that pays for itself three times: a BV inverter

`[C]` Bitwuzla has a single `bv::BvInverter` — 2,402 lines
(`references/bitwuzla/src/solver/bv/bv_inverter.cpp`) covering **21 BV operator
kinds** (`BV_ADD BV_AND BV_ASHR BV_CONCAT BV_EXTRACT BV_MUL BV_NOT BV_OR BV_SGE
BV_SGT BV_SHL BV_SHR BV_SIGN_EXTEND BV_SLE BV_SLT BV_UDIV BV_UGE BV_UGT BV_ULE
BV_ULT BV_UREM`) with the API

```
invert(node, var) -> (inverse_term, side_conditions)
```

and it has **three consumers**:

1. **Quantifier preprocessing** — `PassQuant::find_inverse`
   `[C: src/preprocess/pass/quant.cpp:315-374]` uses it to generalize destructive
   equality resolution: for `(forall x. (or (not A) B))`, any *non-negated*
   equality in `A` mentioning `x` from which an **unconditional** inverse can be
   derived (`conds.empty()`, `:356-361`) gives `x := t` and the body becomes
   `B[x/t]`. For non-BV sorts it degrades to plain DER (`:345-355`).
2. **The quantifier solver** — `d_bv_inverter` again
   `[C: src/solver/quant/quant_solver.cpp:47, :828, :904]`, plus `compute_path`.
3. **The abstraction module's invertibility-condition lemmas** — e.g. `MUL3_IC`
   `(= (bvand (bvor (bvneg s) s) t) t)` (§1.12).

We have inverses in exactly one place and for exactly six operators:
`elim_unconstrained.rs::invert` / `invertible` (`:154-200`), private to that
module, unconditional only. **Extracting a shared `BvInverter` with a
`(term, Vec<Condition>)` return is the single change that unlocks the most
downstream work in this document**: it widens `elim_unconstrained` (§8 item 2),
it is the prerequisite for BV-generalized DER in our quantified divisions, and it
is where the abstraction ladder's IC lemmas (§8 item 10) would come from.

### 5.3 The driver

```
for level in assertion_levels {
    loop {
        modified = false
        for pass in schedule {
            if !enabled(pass) { continue }
            if pass.budget_exhausted() { continue }
            ctx.reset_modified()
            pass.apply(&mut ctx)?
            record_stats(pass, &ctx)
            modified |= ctx.modified()
            if ctx.is_inconsistent() { return Unsat }
        }
        if !modified { break }
    }
}
```

Three properties to copy verbatim from `preprocessor.cpp:236-401`:

- **inconsistency is checked after every pass**, not once at the end;
- **individual passes may have their own inner fixpoint** — Bitwuzla gives one
  to `variable_substitution` alone (`:300-309`), and it is the pass that
  deserves it;
- **run-once and first-call-only gating are first-class**, not a hack:
  `skel_done` (`:257-259`) and `apply_normalization = d_num_preprocess == 1`
  (`:260-261`). Any pass whose cost is superlinear in the assertion set gets one
  of these.

### 5.4 Configuration

One boolean option per pass, plus sub-options for the risky sub-rules, exactly
as Bitwuzla does (`option.cpp:511-568`).

Separately, the **rewriter itself needs a cost grade**. `RewriteRule`
(`crates/axeyum-rewrite/src/lib.rs:205-226`) carries `id`, `name`,
`precondition`, `guard`, `preservation`, `projection`, `tests`,
`enabled_by_default` — richer than Bitwuzla's rule metadata on the *soundness*
axis (we record a preservation class, a model-projection obligation, and a
required test route per rule; Bitwuzla records none of that), but it has **no
cost dimension at all**. Bitwuzla grades every rule `d_level >= 1` / `>= 2`
with `LEVEL_MAX = 2` as the default and a private `LEVEL_ARITHMETIC = 3` used
only inside `normalize`
`[C: references/bitwuzla/src/rewrite/rewriter.h:55-70; 56 `d_level >=` guards throughout
rewriter.cpp, first at :1044, last at :2043]`. Adding a `level: u8` to `RewriteRule` is a one-field
change that buys us a cheap-vs-expensive dial we currently cannot express. The precedent worth copying is that
Bitwuzla ships `pp-variable-subst-norm-diseq` and
`pp-variable-subst-norm-bv-ineq` **off** with a source comment recording that
one of them measured worse. Our `config_registry.rs` is the natural home; note
that `solve_eqs.rs` is already registered there (`config_registry.rs:526`).

### 5.5 Model soundness is not a new problem for us

Every pass here is either denotation-preserving (needs no trail) or eliminates a
symbol with a recorded definition (needs a `trail.define`). Our existing rule —
solve the reduced problem, reconstruct, then **replay against the original
assertions** as the trust anchor (`preprocess.rs`, the comment at lines 74-81) —
covers every pass proposed below without modification. Two passes need a note:

- **Skeleton preprocessing adds assertions, eliminates nothing.** Its new
  assertions are implied by the originals (they are units derived by sound SAT
  propagation over an abstraction that only *loses* constraints), so no trail
  entry is needed and `sat` replay is unaffected. But it must be **disabled when
  producing unsat cores or interpolants**, because the derived assertions have no
  single parent — Bitwuzla says exactly this in a nine-line comment
  (`skeleton_preproc.cpp:94-105`).
- **Slicing replaces `x` by a concat of slice terms**, i.e. it is a
  `trail.define(x, concat)` like any other substitution — with the caveat that
  the fresh slice variables it may introduce must themselves be reconstructable,
  which our orphan-defaulting logic (`elim_unconstrained.rs:363-388`) already
  models.

### 5.6 A cheap IR change that makes every pass skippable in O(1)

Bitwuzla stores a two-bit `NodeInfo{quantifier, lambda}` on every interned node,
OR-ed up from its children at construction
`[C: references/bitwuzla/src/node/node.h:41-53]`. `PassElimLambda::apply` then
skips an entire assertion with `if (assertion.node_info().lambda)`
`[C: src/preprocess/pass/elim_lambda.cpp:37]` — no traversal at all when the
feature is absent.

We do the same query by full DAG walk: `has_quantifier`
(`crates/axeyum-solver/src/auto.rs:1078-1092`) allocates a `BTreeSet` and walks
the forest. Every pass that is a no-op on most inputs pays that walk. A small
bitset on the interned node — "contains quantifier / lambda / array / bvmul /
extract / uninterpreted function", OR-ed from children in `TermArena`'s
interning path — turns the guard on each of §8's proposed passes into a field
read. `[I]` This is the cheapest thing in this document and it makes adding
passes structurally cheap rather than structurally taxed.

### 5.6b Provenance: the `parent` argument is not optional

`AssertionVector::push_back(assertion, parent)` feeds an `AssertionTracker`
`[C: references/bitwuzla/src/preprocess/assertion_tracker.cpp:23-35]` that keeps
two backtrackable maps — assertion → parent, and parent → children — and
supports `find_original` (walk up to an original assertion,
`:37-68`) and `find_children` (walk down to final preprocessed forms,
`:70-100`). It is instantiated **only** when unsat cores or interpolants are
requested (`preprocessor.cpp:48-51`), and the passes that cannot supply a single
honest parent — `skeleton_preproc`, `embedded_constraints`,
`variable_substitution` — **disable themselves entirely** in that mode
(`skeleton_preproc.cpp:101-105`, `embedded_constraints.cpp:37-46`,
`variable_substitution.cpp:619-629`).

That is the honest engineering answer to "preprocessing breaks provenance", and
it matches this repository's stated discipline: a checker that cannot fail is
worse than no checker.

**We are currently immune to this by construction, and that will not last.**
`crate::unsat_core` (`crates/axeyum-solver/src/auto.rs:796-830`) is
*deletion-based*: it re-solves subsets of the **original** assertion indices and
returns indices into them, so no pass has to explain itself. That works and is
determinism-friendly, but it costs one `solve` per assertion, and the moment we
want a core read off a proof — or an interpolant — the provenance edge becomes
mandatory. Take the `parent` argument on `push_back` now, while nothing reads
it, because retrofitting it means touching every pass. And record, per pass,
whether it can supply an honest parent; Bitwuzla's answer for three of its nine
passes is "no, so disable me".

### 5.7 One cheap discipline item worth copying verbatim

Bitwuzla ships a debug-build guard that counts DAG nodes before and after the
whole preprocessing loop and **warns when preprocessing made the problem bigger**
by more than a configurable percentage (`dbg_pp_node_thresh`)
`[C: references/bitwuzla/src/preprocess/preprocessor.cpp:245-253, :402-418]`.
We already compute exactly this number (`PassSize::dag_nodes` in
`crates/axeyum-rewrite/src/pass_stats.rs`); we just never compare it. A pass
that grows the DAG is not necessarily wrong — factoring and div/rem elimination
both do — but it should have to say so.


---

## 6. Indicative prevalence in our committed corpora

**Caveat first, because this number is easy to over-read.** These are file-level
presence counts over the `.smt2` files committed in this repository
(`corpus/public`, `corpus/public-curated`, `corpus/qfbv-curated`), which is a
curated slice, **not** the SMT-LIB divisions we are scored on. It says which
transformations would fire *at all* on what we have locally; it says nothing
about how often they fire per problem, or about the real division.

946 files total; 379 declare a `BV`-family logic, broken down as:
QF_ABV 193, BV 59, QF_AUFBV 53, QF_BV 49, QF_UFBV 10, QF_BVFP 8,
QF_UFBVLIA 6, QF_UFBVFS 1. **Arrays dominate our local BV work** (246 of 379).

| Feature | BV-family files (of 379) | All files (of 946) |
|---|---|---|
| `(_ extract …)` | 63 (17%) | 63 |
| `concat` | 65 (17%) | 65 |
| `bvmul` | 48 (13%) | 48 |
| `bvudiv` | 12 (3%) | — |
| any of `bvule/bvult/bvsle/bvslt` | 51 (13%) | — |
| `(let (` — i.e. authored sharing | 50 (13%) | — |
| top-level `(assert (and …)` | 6 (2%) | 88 (9%) |

Two readings worth carrying into the ranking:

- **Extract/concat/slicing work has a real but bounded local footprint** (~17% of
  BV files). It is not a universal win; it is a win on the structured
  (hardware/decompilation-shaped) subset.
- **`flatten_and` is a cross-division item, not a BV item** here: 6 of 379 BV
  files versus 88 of 946 overall. That inverts the naive assumption and matches
  §1.4's argument — its value is that it *feeds other passes*, and the passes it
  feeds are the general ones (`solve_eqs`, `propagate_values`,
  `embedded_constraints`), which serve every division.


---

## 7. What the literature actually measures — and mostly does not

**The headline is a corrective, so read it before §8.** I asked for quantitative
ablation data on preprocessing passes. It is far thinner than the field's
confidence suggests, and where it exists it is frequently **negative**.

Three findings dominate:

1. **`[P]` The Bitwuzla CAV 2023 paper contains no preprocessing ablation at
   all.** Neither does any Bitwuzla, cvc5, or Yices2 SMT-COMP system description
   from 2022–2025 — **zero of roughly twenty BV-relevant descriptions contains an
   ablation, a solved-instance delta, or a speedup attributable to a
   preprocessing technique.** There is also **no published SMT-COMP competition
   report for 2022, 2023, 2024 or 2025**; the last is Weber et al., *The SMT
   Competition 2015–2018*, JSAT 11(1):221–259, 2019. **The canonical modern BV
   preprocessor has never been measured pass-by-pass in public.**
2. **`[P]` The two best-measured BV preprocessing techniques both came out
   negative in their own authors' evaluations** (slicing as a decision procedure,
   and AIG rewriting before CNF — both below).
3. **`[P]` The strongest positive numbers in this space are not word-level at
   all.** They are CNF-level: bounded variable elimination on bit-blasted BV
   CNFs, and CNF *generation* quality.

`[I]` The implementer's conclusion is uncomfortable: **budget most effort toward
the lowering/CNF path and a small set of cheap, universally-shipped word-level
passes, and treat everything else as opt-in with per-family gating.** That
argues for doing §8's tier-0/tier-1 items (which are cheap and universal) and
being much more cautious about the expensive ones than a "Bitwuzla has it"
argument would suggest.

### 7.1 Two corrections to this lane's own brief

- **Brummayer & Biere, "Local Two-Level And-Inverter Graph Minimization without
  Blowup" (MEMICS 2006) is NOT the source for unconstrained-variable
  elimination.** It is about AIG rewriting and never mentions unconstrained
  variables. The actual sources are **Roberto Bruttomesso, *RTL Verification:
  From SAT to SMT(BV)*, PhD thesis, Trento, 2008** (the BV rule set) and
  **Robert Brummayer, *Efficient SMT Solving for Bit-Vectors and the Extensional
  Theory of Arrays*, PhD thesis, JKU Linz, 2009, §3.4** (independent
  co-discovery, extended to arrays and ITE). `[C]` cvc5 attributes it correctly:
  `references/cvc5/src/preprocessing/passes/unconstrained_simplifier.h` says
  *"Based on Roberto Bruttomesso's PhD thesis."*
- **"Towards Bit-Width-Independent Proofs in SMT Solvers" (Niemetz, Preiner,
  Reynolds, Zohar, Barrett, Tinelli, CADE-27 2019, arXiv:1905.10434) is not
  about word-level normalization.** It translates parametric-width BV into
  quantified `UFNIA`. **But it is directly useful to us for a different reason:**
  its case study (iii) is *verification of the rewrite rules used in SMT
  solvers* — they enumerated 8,024 rewrite candidates with CVC4's SyGuS solver
  and **proved 409 of 435 rewrites correct for all bit-widths**. `[I]` For a
  project whose identity is "trusted small checking", that is the template for
  validating our rewrite manifest **once**, rather than fuzzing it per width.

### 7.2 The measurements that should change our decisions

Ordered by how much they move the ranking.

**Unconstrained-variable elimination — the one clean cross-solver ablation.**
`[P]` Martin Jonáš, Jan Strejček, *"On Simplification of Formulas with
Unconstrained Variables and Quantifiers"*, SAT 2017, LNCS 10491:364–379,
DOI 10.1007/978-3-319-66263-3_23. Three **unmodified** solvers, with and without
the simplification applied as an external preprocessor; all times include
simplification.

| | SMT-LIB `BV1` newly solved | SymDivine newly solved | time vs baseline (SMT-LIB / SymDivine) |
|---|---|---|---|
| Z3 | **+2** | **+195** | **105%** / 18% |
| Boolector | **+8** | **+314** | 84% / **7%** |
| Q3B | 0 | 0 | 75% / 35% |

Cost: *"each formula was simplified in less than 1.3 seconds and the average
simplification time is 0.03 seconds."* Note the **regression**: Z3 on SMT-LIB
went to 105% of baseline, partly simplification cost and partly because *"after
the simplification, Z3's quantifier instantiation heuristics needed more
instantiations."* And Q3B's zero is explained: the 122 unsolved SymDivine
formulas contain no unconstrained variables at all.

`[P]` **Why the SymDivine numbers are so much larger** matters for us:
*"There are basically two sources of unconstrained variables in [symbolic
execution] queries. One source is input variables … The second source is program
variables that are assigned on an executed path, but not read yet. … Such
situations are especially frequent when analyzing Static Single Assignment (SSA)
code such as LLVM."* `[I]` That is exactly the shape of the
symbolic-execution/binary-analysis workloads this project targets (`references/`
carries angr and glaurung clones). **This is the strongest single argument in the
document for §8 item 2.**

**The corner cases, `[P]` from Brummayer §3.4** — write soundness-negative tests
for both: *"`110 · v = 111` must not be replaced"* (multiplication by an **even**
constant), and *"`v < 000` may not be replaced by a fresh Boolean"*
(inequality at the **domain boundary**). The second is why Z3's `bvule` rules
carry the `(or u (= t MAX))` side constraint (§2.4). Brummayer's definition is
also worth quoting exactly: *"We call a variable unconstrained in an SMT formula
`φ` if it has **only one parent in the abstract syntax DAG** representation of
`φ`. **We assume that structural hashing is enabled.**"*

**Slicing — the negative result nobody quotes.** `[P]` Liana Hadarean, *An
Efficient and Trustworthy Theory Solver for Bit-Vectors in SMT*, PhD thesis,
NYU, 2015, §4 (and Hadarean et al., *"A Tale of Two Solvers"*, CAV 2014,
LNCS 8559):

> *"…enabling the core solver that relies on slicing to be complete **hurts
> performance overall**. **The only exception is the `bruttomesso` family of
> benchmarks crafted to stress test core solvers.**"*

The CAV'14 paper hedges to *"it is heuristically turned on for such instances"*.
`[I]` **This is the most important correction to my §8.** Slicing as a *decision
procedure* did not pay for itself outside the family designed to showcase it.
**Slicing as a *substitution enabler* is the version that survived in all three
major solvers** (§1.5.6, §2.9), and that is the version to build.

Two hard constraints on it, both `[P]` from Hadarean §2.2:
- **It is sound only at top level.** Given `v[15:8] = c`, rewriting to
  `v = s ∷ c ∷ s'` introduces *implicitly existentially quantified* Skolems, so
  *"it is not sound to apply this simplification if it is not top-level …
  Applying the simplification under a negation would result in `∀x,x'. v ≠ x ∷ c
  ∷ x'`. This is not equivalent."*
- **Disjointness is the precondition**: *"Given `v[i:j] = t`, it is not sound to
  use `t` to replace `v[i:j]` as it may overlap with other extract terms. If
  however `v[i:j] is a disjoint slice the substitution is safe."* That is exactly
  Bitwuzla's exact-tiling check (§1.5.6).

`[P]` Hadarean also gives a tuning constant worth stealing for our cost gate:
*"We found checking the simplified assertions when they are **less than 50% of
the size of the original assertions** to be a good heuristic."*

The origin and the canonical algorithm, for the record: `[P]` Nikolaj Bjørner &
Mark Pichora, *"Deciding Fixed and Non-fixed Size Bit-vectors"*, TACAS 1998,
LNCS 1384:376–392; and `[P]` Roberto Bruttomesso & Natasha Sharygina,
*"A Scalable Decision Procedure for Fixed-Width Bit-Vectors"*, ICCAD 2009:13–20,
DOI 10.1145/1687399.1687403, which gives the coarsest-base / cut-point algorithm
and the reduction lemma (`p = q` in the extract+concat+equality fragment is
satisfiable iff the per-slice equalities are satisfiable in EUF). Its own
measurements are on **crafted** benchmarks: on `ec` 654 vs 651 baseline, on `sp`
**37 vs 12**, and on `lfsr` (where slicing is not needed) 188 vs 190 — the last
being the overhead control.

**AIG rewriting — the rule set is proven, the application before CNF is not.**
`[P]` Brummayer & Biere, MEMICS 2006, is the source of the four-level table
transcribed at §1.9. Its own measurements (node counts on SMV2QBF k-induction
instances, relative to level 1): O3 gives **up to 25.8%** reduction; **O4's extra
reduction is *"miniscule"***; and greedy local minimization **is not robust** —
it *increased* node counts by up to 14.4% on two families, because *"in one
example the size of a 80k node circuit is increased by 50k nodes using all
possible local optimization rules greedily."* The paper's guarantee is the point:
*"our approach will never increase the number of nodes."* On times, *"O4 results
in more efficient SAT solving than using O3 rules alone."*

But `[P]` Hadarean's thesis §3.3 measured **applying AIG rewriting before CNF**
in CVC4 and found *"the results are mixed, with the performance of cvcE+AIG being
**worse overall**"* — helpful on `brummayerbiere*` (equivalence checking),
**very negative** on `bruttomesso` where *"bit-blasting to AIG **increases the
number of literals in the bit-blasted formula by 20%**"*. `[C]` Z3 agrees in its
own source: `src/tactic/aig/aig_tactic.h` says its simplifications are
*"heuristic, trading speed for power, and **do not represent a high-quality
circuit minimization approach**"*, and it runs `aig` **after** bit-blasting,
wrapped in `if_no_proofs`.

`[I]` Reconciliation: the **rule set** applied at construction time (Bitwuzla's
`rewrite_and`, and ours) is the safe, measured-positive form. A separate
post-construction AIG optimization pass is the form that measured negative.
Since the sibling survey's Rank 4 is *complete the construction-time rule set*,
that recommendation survives; a post-construction pass does not.

**The strongest numbers in the whole survey are CNF-level.**

- `[P]` Bruno Dutertre, *"An Empirical Evaluation of SAT Solvers on Bit-Vector
  Problems"*, SMT 2020, CEUR-WS Vol. 2854:15–25. 41,696 SMT-LIB BV problems
  bit-blasted by Yices 2 — of which **Yices solved 18,940 (45%) without ever
  producing a CNF, "by rewriting and other simplification at the bit-vector
  level."** On the 15,457 non-trivial CNFs, disabling CaDiCaL features
  (default 15,169 solved; noise floor sd 4.59 over 18 seeds, range 15,156–15,176):

  | disabled | solved | impact |
  |---|---|---|
  | **elim (BVE)** | 15,098 | **−71** |
  | stabilize | 15,102 | −67 |
  | rephase | 15,137 | −32 |
  | vivify | 15,161 | −8 |
  | *(default)* | 15,169 | 0 |
  | walk | 15,178 | **+9** |
  | **elimgates** | 15,182 | **+12** |

  **Only the top few rows exceed noise.** `[I]` On bit-blasted BV CNFs, **bounded
  variable elimination is the single most valuable preprocessing pass measured
  anywhere in this document** — and gate-aware BVE, local search and lucky
  phasing are net *harmful*. Also: MiniSAT's weakness traces to its BVE
  clause-size limit — raising it (`--cl-lim=400`) solved **185 more problems**.
- `[P]` Niklas Eén, Alan Mishchenko, Niklas Sörensson, *"Applying Logic Synthesis
  for Speeding Up SAT"*, SAT 2007, LNCS 4501:272–286. CNF via technology mapping:
  **62% average clause reduction** vs plain Tseitin, and *"a **5× speedup** in
  solving for hard industrial problems"* (6.9× without SatELite, 5.3× with, 22.3×
  combined vs plain Tseitin + plain SAT). **The negative half is the more useful
  half**: on SAT-Race benchmarks *"the problems … exhibit a different behavior
  resulting in an **increased runtime** … equivalence checking problems are
  easier to solve if the equivalent points … are kept"* — total speedup 1.0×,
  **harmonic average 0.5×**.
- `[P]` Matti Järvisalo, Armin Biere, Marijn Heule, *"Simulating Circuit-Level
  Simplifications on CNF"*, JAR 49(4):583–619, 2012,
  DOI 10.1007/s10817-011-9239-9. **The theoretical result that reframes the
  question:** starting from **plain Tseitin**, blocked clause elimination
  *"achieves all of the simplifications achieved by … NSI, COI and MIR, and also
  removes those clauses that do not appear in the **Plaisted-Greenbaum**
  encoding"*. BCE is **confluent**; BVE is **not**; they are partially
  orthogonal. And measured **on bit-vector AIG instances generated by
  Boolector**: BCE+BVE on the Tseitin encoding *"removes **more clauses and
  variables than both of Minicirc and NiceDAG** … the numbers of clauses and
  variables produced by NiceDAG are close to **double** the numbers for bebe."*

  `[I]` **This is a direct argument about our own stack.** It says a simple,
  trustworthy Tseitin encoder plus a CNF-level BCE+BVE loop provably subsumes
  Plaisted-Greenbaum and three circuit-level reductions, and empirically beats
  two dedicated circuit-to-CNF encoders on exactly our workload. We already have
  the encoder and `crates/axeyum-cnf/src/bve.rs`. **Whether we have BCE, and
  whether the BVE loop is run on the bit-blasted CNF by default, is the question
  this finding raises — and it belongs to the sibling CNF/SAT lane, not this
  one.**

**Bitwuzla's abstraction module has real ablation data, and it is *negative on
QF_BV*.** `[P]` Aina Niemetz, Mathias Preiner, Yoni Zohar, *"Scalable Bit-Blasting
with Abstractions"*, CAV 2024. Volume: 367,101 multiplications, 55,461 unsigned
divisions, 62,328 unsigned remainders abstracted, of which only **37% / 13% / 2%**
ever needed tier-4 (actual bit-blasting); **80% of solved benchmarks that
abstracted anything were solved without bit-blasting a single abstracted term**;
average 37 refinement iterations, median 4. Disabling the tier-2
(abduction-synthesized) lemmas on `syrew` costs **−336 solved**, 2× more
memory-outs, 23% slower, 61% more memory.

But the authors state the caveat plainly: *"The only significant loss of **−13
benchmarks is in the QF_BV logic**, which is also the only logic where Abstr-t is
significantly slower (33%) on commonly solved instances"* — attributed to `Sage2`
(40% slower) and **`uclid` (4,100% slower)**. Gains concentrate in FP
(QF_FP +23 / −13% time; QF_BVFPLRA +9 / −46%), and on `syrew` it is 12–90×
faster than competitors.

`[I]` **This materially demotes §8 item 9.** The graded lemma ladder is a large
win on floating-point and on `syrew`/`ethereum`-shaped arithmetic, and a small
*loss* on QF_BV proper. Our `lazy_bv` should be enabled per-family, not
globally — and the family where it pays is not the one the brief was aimed at.

**Two general passes with strong numbers and wide reach.**

- **Ackermannization gated by a counting heuristic.** `[P]` Bruttomesso, Cimatti,
  Franzén, Griggio, Santuari, Sebastiani, *"To Ackermann-ize or Not to
  Ackermann-ize?"*, LPAR 2006, LNCS 4246:557–571, DOI 10.1007/11916277_38.
  *"neither DTC nor ACK always prevails … the performance gaps may be
  **dramatic, in either direction**"* (up to 1000× either way). The fix is a
  linear-time count: Ackermannize iff `#ackermann-equalities <
  #interface-equalities`. Measured: transparent 1384 solved / 34,500 s;
  ackermannize 1479 / 41,431 s; **DECIDE 1513 / 12,891 s**; PARTIAL 1516 /
  13,393 s. **+132 solved and ~3× less total time from a counting heuristic**,
  and PARTIAL bought only 3 more than DECIDE. `[I]` **We do eager
  Ackermannization unconditionally (`functions.rs`, ADR-0013). Adding `DECIDE` is
  a counting function, not a new procedure.**
- **Symmetry breaking.** `[P]` Déharbe, Fontaine, Merz, Woltzenlogel Paleo,
  *"Exploiting Symmetry in SMT Problems"*, CADE-23 2011, LNCS 6803:222–236,
  DOI 10.1007/978-3-642-22438-6_18. On all 6,647 SMT-LIB QF_UF problems, veriT
  with symmetry breaking: **6633 solved / 14 timeouts / 5,127 s** versus
  **6570 / 77 / 19,388 s** without — **+63 solved, timeouts 77→14, 2.9× less
  time**, and *"3310 contain symmetries tackled by our method"*. Detection is
  cheap because of Lemma 6: invariance under **all** permutations of `c₀…cₙ`
  follows from invariance under just **two generators**. Two stated limits: the
  gain is on **unsat** (*"no significant trend is observable on satisfiable
  instances only"*), and *"our technique is **inherently non-incremental**."*
- **Input normalization.** `[P]` Amrollahi, Preiner, Niemetz, Reynolds, Charikar,
  Tinelli, Barrett, *"Towards SMT Solver Stability via Input Normalization"*,
  FMCAD 2025, arXiv:2410.22419 — cvc5's `normalize` pass. **Aggregate overhead
  < 0.8%**, unique normal forms for **87%** of a 4,461-benchmark SMT-LIB subset
  (vs 12% for the prior approach), and *"the MAD score improves significantly in
  all cases, sometimes by **more than an order of magnitude**"* with raw
  performance *"generally comparable"*. And a useful partial-credit result:
  *"full normalization is not required for improving stability. An improvement in
  similarity may be sufficient."*

  `[I]` **For a project whose CLAUDE.md lists "determinism is a public API
  promise" as a hard rule, this is arguably the most directly applicable general
  pass in the entire report.** It costs under 1% and buys an order of magnitude
  in run-to-run variance — which is the quantity our frontier ratchet spends
  reference-frame machinery to work around
  (`docs/research/08-planning/frontier-ratchet-reference-frame.md`).

**The price of certified preprocessing, measured.** `[P]` *bv_decide at the
SMT-COMP 2025* (Böving, Bhat, Keizer, Cicolini, Frenot, Mohamed, Stefanesco,
Khan, Clune, Barrett, Grosser) — a Lean-verified solver that *"follows the
approach of the Bitwuzla SMT solver … All rewrite rules are formally verified in
Lean for arbitrary bit-widths."* **QF_BV 2025: `bv_decide` 8,638 vs
`bv_decide-nokernel` 8,862** — kernel-checking the rewrite proofs costs
**224 instances (2.5%)** and roughly **1.5× CPU** (638,058 s vs 426,163 s).
`[I]` That is the published price of the thing this repository exists to do, on
the preprocessing layer specifically. Worth carrying into
`docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md`.

### 7.3 Where preprocessing *is* the whole contribution — SMT-COMP base-deltas

`[P]` Because SMT-COMP scores derived solvers against their own base, the results
tables accidentally contain the best quantitative preprocessing data in the
2022–2025 corpus:

| 2025 QF_BV-family, single query | Solved | Base | Delta |
|---|---|---|---|
| **Bitwuzla-MachBV** (2025 QF_BV winner) | 10,523 | 10,485 | **+38** |
| **z3siri** (synthesized tactic sequences) | 9,308 | 8,944 | **+364** |
| **Z3-Owl** QF_UFBV | 528 | 388 | **+140** |
| **Z3-Owl** QF_BV | 8,656 | 8,541 | **+115** |
| **Z3-alpha** (MCTS tactic synthesis) | 8,970 | 8,945 | +25 |

Bitwuzla-MachBV is XGBoost per-instance strategy selection over Bitwuzla 0.7.0,
and its load-bearing claim is *"**We discovered complementarity among different
preprocessing algorithms and even between different SAT solvers.**"* Its gain is
**entirely on UNSAT (+37); SAT is flat (+1)**.

`[I]` **The contrast between +364 (over Z3) and +38 (over Bitwuzla) is the most
useful number in this table:** Z3's default QF_BV strategy is far from its own
frontier, while Bitwuzla's default is close to it. It also says that
**per-instance pipeline selection is worth 0.4–4% on top of a good default** —
i.e. build the configurable pass framework first (§8 item 0), and treat
scheduling as a later, separate lever.

`[P]` And the cleanest published preprocessing A/B in the whole 2022–2025 corpus
is **essentially null**: STP's 2023 QF_BV entry, whose only reported change was
"improved sharing-aware rewriting", solved **9,847** against the previous year's
binary at **9,846** on the same benchmark set — **+1 instance**, and slightly
*slower* in total CPU.

### 7.4 Five cross-cutting rules the sources converge on

`[I]` These are the design rules I would carry into a brief, each backed above:

1. **Preprocessing and encoding are substitutes, not complements.** Eén & Biere
   (SAT 2005) measured *"reduction rates of less than 5%, and no measurable
   speedup"* on already-well-clausified input. If our BV→AIG→CNF path already
   does structural hashing and sharing (it does), **discount every headline
   preprocessing number in this report.**
2. **Preprocessing is systematically better on industrial instances than crafted
   ones, and is often net-negative on the latter.** `[P]` Wotzlaw, van der
   Grinten, Speckenmeyer (arXiv:1310.4756): the *same* BCE+BVE+UH configuration
   gives **233 vs 184** on 300 application instances and **182 vs 185** on 290
   combinatorial ones. Echoed by Hadarean's AIG result and CAV'24's `uclid`
   regression. **Configure per family, not globally.**
3. **Pass order is load-bearing.** `[P]` Areces, Déharbe, Fontaine, Orbe, *"SyMT:
   finding symmetries in SMT formulas"*, SMT 2013: symmetry detection found
   symmetries in **250** QF_UF instances with no prior simplification and
   **3,638** with trivial syntactic simplification first — **a 14× difference
   from pass order alone.**
4. **Not every pass should run to fixpoint.** Bitwuzla deliberately runs
   `skeleton_preproc` and `normalize` **once** (§1.1). Our `Pass` trait must make
   "run once" and "run to fixpoint" both expressible — that is a design
   requirement on §8 item 0, not an afterthought.
5. **A rewrite that is obviously correct can still be a regression.** `[P]`
   Niemetz & Preiner, *"Ternary Propagation-Based Local Search"*, FMCAD 2020:
   handling `bvslt` natively **lost 262 median solved instances**, because
   rewriting `bvslt` to `bvult` narrows the operand value space that the local
   search exploits on the `uclid` family. Only bound tightening recovered them.
   **Correctness is not sufficiency; measure the downstream consumer.**

### 7.5 Feature interactions: three strategies, and which one fits us

Every mature solver has a "this pass is incompatible with that feature" table,
and the three answers are architecturally different:

| Solver | Strategy | Evidence |
|---|---|---|
| **Z3** | **Disable the pass.** `bv-size-reduction`, `ackermannize_bv` and `aig` are wrapped in `if_no_proofs(if_no_unsat_cores(...))`; `solve-eqs` and `elim-uncnstr` are skipped in incremental mode. | `[C: qfbv_tactic.cpp:68,79]`, §2.11 |
| **cvc5** | **Disable the pass, but prove the rest.** `unconstrainedSimp` is `incompatibleWithModels` and force-disabled for incremental (verified: `SET_AND_NOTIFY(smt, unconstrainedSimp, false, "incremental solving")`, `references/cvc5/src/smt/set_defaults.cpp:1235`); yet TACAS'22 claims proofs for *"nearly all… preprocessing passes"*. | `[C]`/`[P]` |
| **Bitwuzla** | **Both.** An `AssertionTracker` gated on `produce_unsat_cores()` plus `post_process_unsat_core` tracing cores back through preprocessing (§5.6b) — **and** the three passes that cannot supply an honest parent disable themselves anyway. | `[C: preprocessor.cpp:48-51, :160-228]`, `[C: skeleton_preproc.cpp:101-105]` |

`[I]` **Bitwuzla's is the strategy that fits this project's stated identity.**
"Disable the pass when evidence is requested" means the evidence-producing
configuration is *not the configuration you benchmarked* — precisely the class of
blind spot CLAUDE.md's Gotchas section exists to catch. Track the provenance
edge (§5.6b), and where a pass genuinely cannot supply one, disable it *and say
so in the artifact*.

Two soundness constraints to encode from day one, both `[P]`:

- **Never eliminate a theory literal at the SAT level, and never eliminate the
  bits of input variables when a model is requested** (Hadarean, citing Eén &
  Biere). This is why CVC4 uses a *separate* SAT solver for bit-blasting.
- **Variable slicing is unsound under a negation** — the fresh slices are
  implicitly existentially quantified. **Top level only.**

### 7.6 What I looked for and did not find

Recorded so the next lane does not spend the hours again:

- No preprocessing ablation for Bitwuzla or Boolector, in CAV'23, JSAT'15, or any
  SMT-COMP description 2022–2025.
- No published SMT-COMP competition report for 2022–2025.
- No paper behind cvc5's `bv_gauss` (verified: no citation in the source, unlike
  `ackermann.cpp` which cites Hadarean; `references/cvc5/src/options/bv_options.toml`
  gives `category = "expert"`, `default = "false"`). No measured evaluation
  anywhere. `[I]` Do not build it on the strength of "cvc5 has it".
- No measured ablation of the LRA Gaussian presimplification (Dutertre & de
  Moura, CAV 2006, §3 *is* titled "Preprocessing" and says *"in practice, this
  presimplification can reduce the matrix size significantly"* — but never with a
  number, in either the paper or tech report CSL-06-01).
- No measured ablation of the LIA equality-elimination handler (Griggio,
  JSAT 8(1/2):1–27, 2012).
- No head-to-head of **static vs dynamic** Ackermannization anywhere. Yices's
  *"dramatic performance benefit"* is asserted without numbers, and Z3 warns that
  dynamic Ackermann reduction can be *"detrimental"* when formulas are expected
  to be satisfiable.
- The CAV'14 "Tale of Two Solvers" ablation figures are **scatter plots with no
  numbers in the text**.


---

## 8. Ranked recommendations

Ranking criterion: (breadth across our 12 divisions) × (**measured** payoff at a
reference solver) ÷ (effort, given what we already have). Effort is lane-days for
one lane, my estimate, `[I]`.

**Read §7 first.** The evidence base is thinner and more negative than the pass
lists suggest, and three items below moved because of it. The **Evidence** column
records what actually backs each item; `none published` is a real and common
answer, and it is not a reason to skip an item — it is a reason to instrument it
(item 0) rather than to assume.

| # | Item | Effort `[I]` | Breadth | Evidence | New here? |
|---|---|---|---|---|---|
| 0 | Pass framework: trait, assertion vector, driver, **per-pass stats** | 2-3 d | all 12 | — (it is what *produces* evidence) | **yes** |
| 0b | Cached structural bitset on interned nodes | 0.5 d | all 12 | — | **yes** |
| 1 | `flatten_and` + `embedded_constraints` | 1 d | all 12 | none published; universal in solvers | **yes** |
| 2 | Widen `elim_unconstrained` past 6 ops | 2-3 d | all 12 | **strong** — Boolector +8/+314, Z3 +2/+195, 0.03 s avg cost | **yes** |
| 2b | Shared `BvInverter` (3 consumers) | 3-4 d | BV + quantified | structural (both Z3 and Bitwuzla factored it out) | **yes** |
| 2c | Alpha-*normalizing* entry point in `alpha.rs` | 0.5 d | quantified | — | **yes** |
| 3 | Extract through `bvadd`/`bvmul` | 0.5 d | BV/ABV/AUFBV | none published; **independently in both** Z3 and Bitwuzla | **yes** |
| 3b | Ackermannization gated by `DECIDE` | 1-2 d | QF_UF, UF, QF_AUFBV, QF_UFBV | **strong** — **+132 solved, ~3× less time** | **yes** |
| 3c | Input normalization | 2 d | all 12 | **strong** — <0.8% overhead, **order-of-magnitude** variance reduction | **yes** |
| 4 | Gaussian elimination in `solve_eqs` | 2 d | BV (+ pattern for LIA/LRA) | none published; **independently in both** | **yes** |
| 4b | `bv-divrem-bounds` (additive bound lemmas) | 0.5 d | BV/ABV | none published; always-on in Z3's preamble | **yes** |
| 4c | Disjoint-bitfield `bvadd => bvor`; `isolate_term` | 1 d | BV | Z3 states *"much cheaper to bit-blast"* in source | **yes** |
| 5 | Skeleton preprocessing | 1-2 d | most | none published | already ranked elsewhere |
| 6 | `max_bv_sharing` | 1-2 d | BV | none published | **yes** |
| 7 | Variable slicing (**substitution-enabler form only**) | 3-4 d | BV | **mixed/negative** for the decision-procedure form | **yes**, but demoted |
| 8 | Complete AIG two-level rules (construction-time) | — | all bit-blasted | **strong** — up to 25.8% node reduction at O3 | already ranked elsewhere |
| 9 | Per-pass budgeted cost gating + factoring | 2-3 d | BV | structural | partly new |
| 10 | Graded lemma ladder for `lazy_bv` | 4+ d | **FP first**, not QF_BV | **mixed** — big FP win, **−13 on QF_BV** | **yes**, but re-aimed |
| — | Symmetry breaking | 3+ d | QF_UF, QF_IDL, QF_LIA, AUFLIA | **strong** — +63, timeouts 77→14, 2.9× | out of scope, see §8.4 |
| — | CNF-level BCE after plain Tseitin | — | all bit-blasted | **strong on size, inconclusive on time** | **already Rank 2b elsewhere**, see §8.4 |

### 8.1 Tier 0 — do this first; everything else depends on it

**0. The pass framework** (§5). The pipeline exists **twice with different
semantics** — `preprocess.rs:78-134` iterates `MAX_PREPROCESS_ROUNDS = 8`;
`auto.rs:1933-1975` runs the same four passes exactly once — and there is nowhere
to put a tenth. Ship `Pass`, `PassCtx`, `AssertionVector`, one owned
`ModelReconstructionTrail`, a shared incremental occurrence index, per-pass
timers and size deltas, one config flag per pass, and the `parent` provenance
edge (§5.6b). Delete the second copy.

Two design requirements that come from the evidence, not from taste:

- **"run once" and "run to fixpoint" must both be expressible.** Bitwuzla
  deliberately runs `skeleton_preproc` and `normalize` once (§1.1, §7.4 rule 4).
- **The per-pass statistics are the deliverable.** §7 is the finding that
  **nobody has published a pass-level ablation for a modern BV preprocessor.**
  Every "which pass matters" claim in this document is someone else's, on someone
  else's corpora. After item 0 lands we can answer it on ours in one bench run —
  and that measurement would be a genuinely novel public artifact, not just
  internal tuning.

**0b. A cached structural bitset on interned nodes** (§5.6). Two-to-six bits per
node ("contains quantifier / lambda / array / bvmul / extract / UF"), OR-ed from
children at interning. Turns every pass's "is this relevant?" guard from a DAG
walk (`has_quantifier`, `auto.rs:1078-1092`) into a field read.

### 8.2 Tier 1 — measured payoff, cross-division, small

**1. `flatten_and` + `embedded_constraints`** (§1.4, §1.7). ~70 and ~125 lines in
Bitwuzla, neither BV-specific. `flatten_and` is a force multiplier: it is what
exposes equalities to `solve_eqs` and `propagate_values`, which we already have
and which serve every division. **Z3 promotes the same operation into the
framework itself** as `flatten_suffix()`, run between *every two passes* (§2.6) —
which is a stronger endorsement than a pass list. 88 of 946 local corpus files
have a top-level `(assert (and …))` (§6), and that undercounts, because it cannot
see conjunctions that appear only after substitution.

**2. Widen `elim_unconstrained` beyond the six invertible BV ops.** *This is the
best-evidenced item in the document.* Ours covers `bvnot/bvneg/bvadd/bvxor/bvsub`
and odd-constant `bvmul` (`elim_unconstrained.rs:154-158`). Z3's covers Booleans,
ITE, comparisons, arrays, datatypes, sequences and **all of arithmetic** — and
the arithmetic table (§2.4) fires in QF_LIA/QF_LRA/QF_IDL/QF_NIA/QF_NRA, where we
currently have no word-level reduction of this kind at all.

Jonáš & Strejček measured it across three unmodified solvers: **Boolector +8
(SMT-LIB) / +314 (SymDivine), Z3 +2 / +195**, at **0.03 s average cost** (§7.2).
And the workload where it pays most is symbolic execution over SSA code — which
is this project's stated consumer track.

Three things to do at the same time:
- **The incremental worklist** (§2.2): a min-heap on parent count, `set_root`
  transplanting the parent list, and `return` (not `continue`) once the minimum
  exceeds one parent. Z3's design note describes our current implementation as
  the problem it was written to fix.
- **The two soundness corner cases** as negative tests (§7.2): `bvmul` by an
  **even** constant, and inequalities at the **domain boundary** (which is why
  the `bvule` rules carry the `(or u (= t MAX))` side constraint).
- **`mk_diff`'s guard**: refuse on an uninterpreted or one-element sort
  (§2.3). The counterexample is in Z3's source and is worth a test verbatim.

**2b. Extract a shared `BvInverter`** (§5.2b). **Both** Z3 and Bitwuzla factored
inversion into a separate component with several consumers — Z3's is even a
per-theory plugin registry with an injected "is unconstrained?" predicate. Ours
is a private six-operator function. Give it the
`(inverse_term, Vec<SideCondition>)` signature from the start even if the first
consumer only accepts `conditions.is_empty()`, as `PassQuant::find_inverse` does.
It unlocks item 2, BV-generalized DER for our quantified divisions, and the
lemma ladder of item 10.

**2c. An alpha-normalizing entry point in `alpha.rs`** (§1.10b). We export only
predicates; Bitwuzla normalizes binders to a canonical variable per type so
alpha-equivalent formulas intern to the same node. Turns pairwise comparison into
hash-consing and makes the sharing available to every downstream pass.

**3. Extract pushed through `bvadd`/`bvmul`** (§3.1). One recursive rewrite next
to the six extract rules we already have (`canonical.rs:2430-2497`). **Z3 and
Bitwuzla implement it independently with the same `lo == 0` carry-independence
guard** — that convergence is the evidence. It turns a `w`-bit multiplier whose
top bits are discarded into a `(u+1)`-bit one, quadratically cheaper.

**3b. Ackermannization gated by `DECIDE`** (§7.2). We Ackermannize eagerly and
unconditionally (`functions.rs`, ADR-0013). LPAR 2006 measured that the choice
matters *"dramatically, in either direction"* (up to 1000× each way) and that a
**linear-time counting heuristic** — Ackermannize iff `#ackermann-equalities <
#interface-equalities` — recovers essentially all of it: **1384 → 1513 solved and
34,500 s → 12,891 s**. The refined `PARTIAL` variant bought only 3 more, so
**build `DECIDE`, not `PARTIAL`.** This is a counting function over a pass we
already own.

**3c. Input normalization** (§7.2). `[I]` The item I would not have proposed
without the literature. cvc5's `normalize` pass costs **< 0.8% aggregate
overhead** and improves run-to-run stability *"sometimes by more than an order of
magnitude"* with raw performance comparable. **CLAUDE.md lists "determinism is a
public API promise" as a hard rule**, and our frontier ratchet spends real
machinery on reference frames and NOT-COMPARABLE markings to work around
variance (`docs/research/08-planning/frontier-ratchet-reference-frame.md`).
A pass that attacks the variance directly, at under 1%, is unusually well matched
to this repository. Note the partial-credit result: *"full normalization is not
required for improving stability. An improvement in similarity may be
sufficient."*

### 8.3 Tier 2 — good, more work, or weaker evidence

**4. Gaussian elimination in `solve_eqs`** (§3.3, §2.7). ~150 lines including the
2-adic inverse. **Z3 and Bitwuzla implement the same rules independently**, and
it strictly subsumes our current bare-variable case. The *idea* (solve a linear
form for one variable) transfers to QF_LIA/QF_LRA/QF_IDL, where Z3's
`arith_extract_eq` gives the concrete rules (§2.7) — including `mod` elimination.

**4b. `bv-divrem-bounds`** (§2.9). The cheapest useful thing in this document:
walk the ground subterms and, for each div/rem with a **symbolic** divisor, add
one bounding clause. **Additive, valid (no model converter), proof-supporting**
(`supports_proofs() == true`), and always on in Z3's QF_BV preamble. The
rationale in Z3's own header is the argument: *"Bit-blasting a division circuit
with a symbolic divisor hides the algebraic fact that the remainder magnitude is
bounded by the divisor magnitude."*

**4c. Disjoint-bitfield `bvadd => bvor`, and `isolate_term`** (§2.10). Two
`bv_rewriter` rules with clear cost arguments: the first removes an entire carry
chain when bit-position analysis shows at most one operand can be non-zero; the
second is `(= C (bvadd t₁ .. tₙ)) => (= t₁ (bvsub C (bvadd t₂..tₙ)))`, whose
justification Z3 states in source — *"it is much cheaper to bit-blast."*

**5. Skeleton preprocessing** (§1.6) — **already recommended in
`pipeline-survey-2026-09/bitblasting-and-aig.md` §2.8.** Listed here only to add
a second argument for the same work: it is the cheapest way to hand *new
top-level facts* to the word-level passes above. Must be disabled when producing
unsat cores or interpolants (§5.5).

**6. `max_bv_sharing`** (§2.9). Reassociate n-ary `bvadd/bvmul/bvor/bvand` so
chains sharing a sub-multiset parenthesize **identically**, making the shared
adder or multiplier one hash-consed term. Our AC path sorts by `TermId`, which is
a *canonical* order, not a *sharing-maximizing* one. Z3's algorithm is 70 lines
and the data structure is `HashSet<(DeclId, TermId, TermId)>` with the pair
sorted — cheaper and simpler than Bitwuzla's `normalize_adders` (§1.8.1) for the
same goal. Watch the O(n³) restart loop; Z3 caps it at 128 operands.

**7. Variable slicing — demoted, and re-scoped.** `[P]` CVC4 measured the
slicing-based *core solver* as **hurting performance overall**, helping only the
`bruttomesso` family crafted to showcase it (§7.2). What survived in all three
major solvers is slicing as a **substitution enabler**: cut the variable at the
extract boundaries, and if the slices tile it exactly, substitute the whole
variable away. Build **that**, with both stated guards:
**top-level only** (the fresh slices are implicitly existentially quantified, so
the rewrite is unsound under a negation) and **exact tiling / disjointness**.
Implement **Bitwuzla's** version (§1.5.6), not Z3's — Z3's `bv_slice` has no
fixpoint and its own header says it is *"not fully implementing a full slicing"*,
and it ships **default off**.

**8. Complete the AIG two-level rules** — **already Rank 4 in the sibling
survey**, with the same table. The literature adds the number and the caveat: the
MEMICS'06 rules give **up to 25.8% node reduction at O3**, O4 adds *"miniscule"*
extra reduction, and **greedy application is not robust** (it *increased* one
80k-node circuit by 50k nodes). Crucially, this is the **construction-time** rule
set. A *separate post-construction AIG optimization pass* is a different thing,
and CVC4 measured that as **worse overall** (§7.2) — so do not let this item
grow into that one. **Defer to the sibling doc; do not open a second lane.**

**9. Per-pass budgeted cost gating, plus the factoring rules** (§1.8, §3.2).
Smaller than I first thought, because the oracle exists:
`reduction_shrinks_encoding` (`auto.rs:1975-2010`) already accepts or rejects the
whole reduction by lowered AIG size. Two changes: make it **budgeted and
interleaved** rather than lowering both sides fully, and move the decision from
once-per-pipeline to **once-per-candidate** — which is what makes the factoring
rules of §3.2 safe to enable, since `NORM_FACT_BV_SHL_MUL` is an explicit cost
inversion (two barrel shifters for one multiplier).

### 8.4 Re-aimed, and out of scope

**10. The graded lemma ladder for `lazy_bv` — re-aim it at floating-point.**
CAV 2024 gives real ablation data (§7.2): 80% of benchmarks that abstracted
anything were solved **without bit-blasting a single abstracted term**, and
disabling the abduction-synthesized lemmas costs **−336 solved** on `syrew`.
**But the authors state the QF_BV caveat plainly: −13 benchmarks, 33% slower on
commonly solved instances, with `uclid` 4,100% slower.** The gains concentrate in
**QF_FP (+23 solved, −13% time) and QF_BVFPLRA (+9, −46%)**.

`[I]` So the honest recommendation is not the one the brief was aimed at. Two
sub-tasks, in order: **(a) enable our existing `lazy_bv` per-family and measure**
— it is off by default (`backend.rs:224-232`) and we have never measured what the
blunt version buys; **(b) build the ladder only if (a) shows the FP and
wide-arithmetic families respond.** Do not turn it on globally for QF_BV.

**Symmetry breaking — a QF_UF item, not a BV one, and worth its own lane.**
`[P]` veriT on all 6,647 SMT-LIB QF_UF problems: **+63 solved, timeouts 77 → 14,
2.9× less cumulative time**, with symmetries present in 3,310 of them, and
detection made cheap by a two-generator lemma (§7.2). SyMT found symmetries
across QF_IDL, QF_LIA, QF_LRA and AUFLIA too. Two caveats: **the gain is on
unsat** and the technique is *"inherently non-incremental"*. Out of this
document's scope, but it is the largest untouched cross-division number I found.

**CNF-level BCE after plain Tseitin — already owned, and my literature adds one
number to it.** `pipeline-survey-2026-09/bitblasting-and-aig.md` **Rank 2b**
already recommends blocked clause elimination, confirms we do not have it (the
only `blocked_clause` hit in `crates/` is a DRAT checker test at
`crates/axeyum-cnf/src/drat.rs:1299-1307`), and carries a better-scoped
measurement than mine — 3,672 bit-blasted QF_BV instances, BCE on plain Tseitin
at 420 M vars / 1,119 M clauses against Plaisted-Greenbaum's 442 M / 1,153 M —
plus a caveat I did not have: **the paper's QF_BV solve-time experiments were run
at 90 s and reported inconclusive.** Its soundness argument is also the right one
(BCE only deletes, so a detector bug cannot produce a wrong `unsat`).

What §7.2 adds to that item, and only that: `[P]` Järvisalo–Biere–Heule's
**theorem** that BCE on plain Tseitin subsumes Plaisted-Greenbaum, cone-of-influence,
non-shared-input **and** monotone-input reduction; and `[P]` Dutertre's separate
measurement that **BVE is the single most valuable CaDiCaL feature on
bit-blasted BV CNFs (−71 solved when disabled**, noise floor ±5) — which says the
*pairing* BCE+BVE is what the JAR paper measured, and BVE is the half with a
solve-time number. We already have `crates/axeyum-cnf/src/bve.rs`; whether it
runs by default on the bit-blasted CNF is a question for that lane.
**Hand these two facts to whoever owns Rank 2b; do not open a lane here.**

### 8.5 Explicitly not recommended

- **Disequality normalization** (`(not (= x e))` → `(= x (bvnot e))` at width 1).
  Bitwuzla ships it off with the source comment *"This is worse on FP, and
  overall does not yield an improvement"* `[C: variable_substitution.cpp:511]`.
- **`elim_udiv`-style BV div/rem elimination.** Disabled in Bitwuzla's source
  behind `if (false && ...)` `[C: preprocessor.cpp:355-356]` pending a bug. Do
  not port it on the strength of "Bitwuzla has it" — Bitwuzla does not run it.
  (`bv-divrem-bounds`, item 4b, is a **different and much cheaper** thing.)
- **`bv_gauss`-style modular Gaussian elimination over `(Σ aⱼxⱼ + b) mod p`.**
  cvc5 ships it `category = "expert"`, `default = "false"` (verified in
  `references/cvc5/src/options/bv_options.toml:86-90`), with **no citation in
  the source and no published evaluation anywhere**. The SAT analogue measured
  **1–5%** on its own target workload.
- **N-ary AND / native XOR CNF encodings, the ITE-extraction sharing guard, and
  Plaisted-Greenbaum.** All four are already in `crates/axeyum-cnf`
  (`encode_and_tree_gate:3887`, `encode_xor_gate:3718`,
  `plan_xor_and_not_ite_gates:3519-3545` requiring `use_counts[helper] == 1`, and
  the `encode_forward`/`encode_reverse` split). The first two are Bitwuzla TODOs.
  **We are ahead on the AIG→CNF encoder; the gap is on AIG construction (§4.3)
  and above it.**
- **A post-construction AIG optimization pass** (as opposed to completing the
  construction-time rules). CVC4 measured it *worse overall*, with a **20%
  increase in literals** on one family, and Z3's own source calls its `aig`
  tactic *"heuristic … not a high-quality circuit minimization approach"*.

### 8.6 The honest summary

`[I]` If I had to reduce this to one paragraph for a dispatcher: **build the pass
framework and its per-pass statistics (item 0), because the field has no public
pass-level ablation for a modern BV preprocessor and we would be the first to
have one on our own corpora. Then do the cheap universal passes — `flatten_and`,
`embedded_constraints`, the widened unconstrained elimination behind a shared
inverter, the extract-through-arithmetic rewrite, the `DECIDE` gate on
Ackermannization, and input normalization — all of which are small, and three of
which have real measured payoff. Treat slicing, the lemma ladder, and
cost-gated normalization as opt-in and per-family, because their published
evidence is mixed or negative. And note that the two largest measured numbers in
this whole survey are not word-level at all: CNF-level blocked-clause and
variable elimination, which is already Rank 2b in the sibling survey — hand it
the two facts in §8.4 rather than opening a lane here.**

