# SMT-level (word-level) preprocessing: what frontier BV solvers do before bit-blasting

**Lane:** `research-smt-preproc` (read-only research lane, 2026-09-08)
**Sibling file in this directory:** `cadical-kissat-budget-model.md` (SAT-side budget model, different lane).

**Claim tags used throughout.** `[C]` = read in solver source, with `file:line`.
`[P]` = from a paper or system description. `[I]` = my inference, not verified.
Where I did not verify something, the text says **did not verify** rather than
guessing.

**Source trees read.** Shallow clones placed in the gitignored `references/`:

- `references/bitwuzla` — `bitwuzla/bitwuzla` @ `a5e6e8a7ad511975c495455924d0868bcdc304ea` (2026-09-04)
- `references/z3` — `Z3Prover/z3` @ `e18d63bda04fcab8240eb55314d567db3e43d540` (2026-09-08)

Both were cloned by this lane with `git clone --depth 1`; `scripts/fetch-references.sh`
already lists both, they were simply not present on this host.

All `file:line` citations below are relative to those two directories unless the
path starts with `crates/`, which means this repository.

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
> directions of every AND (`aig_cnf.cpp:319-335`). The one thing worth borrowing
> from Bitwuzla's encoder is its **sharing guard**: it refuses the ITE
> extraction when an inner node has more than one parent (`aig_cnf.cpp:182-198`).

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
  cheap partial lemmas** — 19 for `MUL`, 37 for `UDIV`, and a UREM family
  `[C: enum LemmaKind, src/solver/abstract/abstraction_lemmas.h]` — e.g.

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

