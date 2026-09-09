# Technique inventory: Bitwuzla and the SAT layer

**Lane:** `inventory-bitwuzla-sat` · **Date:** 2026-09-09 · **Status:** inventory only

This document is one side of a diff. It enumerates what Bitwuzla, Kissat and
CaDiCaL *implement*. It deliberately makes **no comparison to axeyum** and
**no ranking by importance** — a sibling synthesis lane owns both. Read it as a
catalogue, not as a plan.

## Method and its limits

Everything below was read out of the gitignored reference clones in
`references/` (repopulate with `scripts/fetch-references.sh`). Where a published
paper and the shipping source disagree, **the source wins and the disagreement
is recorded as a finding**.

| Subject | Clone | Version | HEAD |
| --- | --- | --- | --- |
| Bitwuzla | `references/bitwuzla` | `0.9.1-dev` (`meson.build`) | `a5e6e8a` 2026-09-04 |
| Kissat | `references/kissat` | `4.0.4` (`VERSION`) | `8af8e56` 2025-10-16 |
| CaDiCaL | `references/cadical` | see §3 | `c607304` 2026-07-19 |

All three clones are **shallow (depth 1)**. `git log -S` and file-history
archaeology therefore return nothing; every "removed in version X" claim below
comes from `NEWS.md` or from a comment still in the tree, never from history,
and is marked accordingly.

Provenance column: `[C]` = read in the source; `[P]` = stated by a paper,
`NEWS.md`, or a commit message; `[I]` = inference from surrounding code.
"Did not verify" appears wherever it is the honest answer.

---

# 1. Bitwuzla

## 1.1 Preprocessing passes — the literal list

The full pass set is the nine members of `Preprocessor` at
`references/bitwuzla/src/preprocess/preprocessor.h:118-126`. There are no
others; the class has no plugin registry. The fixed-point loop that runs them is
`Preprocessor::apply`, `references/bitwuzla/src/preprocess/preprocessor.cpp:237`.

| # | Pass | Entry point | Option / default | What it does | Prov |
| --- | --- | --- | --- | --- | --- |
| B1 | Rewrite | `src/preprocess/pass/rewrite.cpp:23` | **always on**, no option guard | Applies the term rewriter to every assertion; the only pass with no `if` around it. | `[C]` |
| B2 | Flatten AND | `src/preprocess/pass/flatten_and.cpp:31` | `--pp-flatten-and`, **on** (`option.cpp:523`) | Splits top-level `and` chains into separate assertions so later passes see more top-level facts. | `[C]` |
| B3 | Variable substitution | `src/preprocess/pass/variable_substitution.cpp:615` | `--pp-variable-subst`, **on** (`option.cpp:538`) | Top-level-equality substitution with cycle breaking; the single largest pass (1380 lines). | `[C]` |
| B4 | Skeleton preprocessing | `src/preprocess/pass/skeleton_preproc.cpp:90` | `--pp-skeleton-preproc`, **on** (`option.cpp:533`) | Bit-blasts only the **Boolean skeleton** to CNF, runs CaDiCaL `simplify()`, harvests root-level fixed literals back as term-level facts. | `[C]` |
| B5 | Embedded constraints | `src/preprocess/pass/embedded_constraints.cpp:33` | `--pp-embedded`, **on** (`option.cpp:518`) | Replaces occurrences of a top-level assertion *inside* another assertion with `true`. | `[C]` |
| B6 | Lambda elimination | `src/preprocess/pass/elim_lambda.cpp:31` | **always on**, no option guard | Beta-reduces applications of lambda nodes. | `[C]` |
| B7 | `bvudiv`/`bvurem` elimination | `src/preprocess/pass/elim_udiv.cpp:31` | `--pp-elim-bvudiv`, **off** (`option.cpp:513`) — and **dead**, see §1.2 | Would rewrite division/remainder into a multiply-plus-constraint encoding. | `[C]` |
| B8 | Arithmetic normalization | `src/preprocess/pass/normalize.cpp:1252` | `--pp-normalize`, **on** (`option.cpp:528`) — but gated three more ways, see §1.3 | Occurrence-counted normalization of `bvadd`/`bvmul` chains, accepted only if an AIG-size estimate improves. | `[C]` |
| B9 | Quantifiers | `src/preprocess/pass/quant.cpp:33` | `--pp-quant`, **on** (`option.cpp:564`) | Quantifier-specific rewriting; sub-option `--pp-quant-alpha` (**on**) merges alpha-equivalent quantifiers. | `[C]` |

The loop runs B1..B9 to a fixed point (`do { ... } while (modified && !inconsistent && !terminate)`),
with **B3 wrapped in its own inner fixed point** — variable substitution repeats
until it stops changing anything before control moves on
(`preprocessor.cpp:298-311`). Two passes are one-shot rather than fixed-point:
B4 runs only on the *initial* assertions (`skel_done` at `preprocessor.cpp:255`),
and B8 runs only on the **first** `preprocess()` call
(`apply_normalization = d_num_preprocess == 1`, `preprocessor.cpp:261`) because
it is judged too expensive for incremental use.

`Preprocessor::process` (`preprocessor.cpp:152`) is a **reduced pipeline** used
to push a single new term through what has already been decided: rewrite →
variable substitution → lambda elimination → embedded constraints → rewrite.
Only five steps of the nine, and the rewriter runs twice.

## 1.2 Passes that are present but do not run — the highest-value rows

| Finding | Evidence | Prov |
| --- | --- | --- |
| **`elim_udiv` is dead code, not merely default-off.** The call site is `if (false && options.pp_elim_bv_udiv())` — the option cannot enable it. The comment says "Disabled until murxla-c598aa85aefc51a0.min.smt2 is fixed", i.e. a fuzzer (Murxla) found a bug and the pass was switched off at the call site rather than fixed or deleted. 177 lines of unreachable code ship in every build. | `src/preprocess/preprocessor.cpp:355-356` (comment at :354) | `[C]` |
| **Extract elimination was deleted, and the CAV 2023 pass list is stale.** `NEWS.md:33` for 0.9.1: "Removed obsolete option `--pp-elim-extracts`. This preprocessing pass is now subsumed by the variable substitution preprocessing pass." There is no `elim_extract.*` in `src/preprocess/pass/`. Confirms the prior reading: **do not copy a paper's pass list, read the directory.** | `references/bitwuzla/NEWS.md:33`; directory listing | `[C]`+`[P]` |
| **Contradicting-ANDs elimination was deleted for measuring zero.** Unreleased `NEWS.md` entry: "Removed obsolete option `--pp-contr-ands`. This preprocessing pass was disabled by default and does not have an observable positive impact." A named technique its own authors measured as worthless. | `references/bitwuzla/NEWS.md:12-13` | `[P]` |
| **`bvxor` and `bvcomp` are deliberately NOT eliminated to core operators.** Two commented-out lines sit in the elimination table: `// BZLA_ELIM_KIND_IMPL(bv_xor, BV_XOR_ELIM) do not eliminate` and `// BZLA_ELIM_KIND_IMPL(bv_comp, BV_COMP_ELIM)`. Every other of 39 derived BV operators is eliminated. The XOR one carries an explicit "do not". | `src/rewrite/rewriter.cpp:1600-1602` | `[C]` |
| **Three abstraction targets exist but are off by default**: `--abstraction-bvadd` (**off**), `--abstraction-ite` (**off**), `--abstraction-inc-bitblast` (**off**). The full `ADD_*` lemma family (13 schemas) and the ITE expand/refine path are compiled but unreachable at default settings. | `src/option/option.cpp:417`, `:437`, `:412`; lemma kinds at `src/solver/abstract/abstraction_lemmas.h` | `[C]` |
| **Assertion abstraction is off by default and is force-disabled in one configuration.** `--abstraction-assert` defaults false, and `option.cpp:959` sets it back to false unconditionally in a branch whose comment reads "Assertion abstraction adds back assertions as lemmas, which is generally [ ... ]" — I did not read the full comment. | `src/option/option.cpp:395`, `:955-959` | `[C]` |
| Two disequality/inequality normalizations inside variable substitution are default-off: `--pp-variable-subst-norm-diseq` (**off**) and `--pp-variable-subst-norm-bv-ineq` (**off**). Only `--pp-variable-subst-norm-eq` (Gaussian elimination) is on. | `src/option/option.cpp:543-563` | `[C]` |
| Local-search option `--prop-opt-lt-concat-sext` (inverse-value optimization for inequalities over concat/sign-extend) is **off**. | `src/option/option.cpp:349` | `[C]` |

## 1.3 Techniques inside the passes

| Name | File:line | Default | What it does | Prov |
| --- | --- | --- | --- | --- |
| Gaussian elimination over BV equalities | `src/preprocess/pass/variable_substitution.cpp:156` (`normalize_substitution_eq`), stat at `:186` | on (`--pp-variable-subst-norm-eq`) | Solves a linear BV equality for one variable so it can be substituted; counted separately as `normalize_eq::num_gauss_elim`. | `[C]` |
| Linear-equation normalization | same file, stat `num_norm_eq_linear_eq` at `:1319` | on | Second normalization route counted alongside Gaussian elimination. | `[C]` |
| Concat-aware equality splitting | `src/preprocess/pass/variable_substitution.cpp:451` (`normalize_substitution_eq_bv_concat`) | on | Splits `x = concat(a,b)` style equalities into per-slice substitutions. | `[C]` |
| **Non-overlapping extract substitution** | `src/preprocess/pass/variable_substitution.cpp:1089` (`process_extracts`), helper `compute_non_overlapping` at `.h:86` | on | Partitions the extracts of a variable into non-overlapping ranges and substitutes the variable by a concat of fresh slice variables. **This is what replaced the deleted `--pp-elim-extracts` pass.** | `[C]` |
| Substitution cycle breaking | `.h:46` `remove_indirect_cycles`, `.h:48` `is_direct_cycle` | on | Rejects substitutions that would make the map cyclic; distinguishes direct from indirect cycles. | `[C]` |
| Substitution safety by assertion index | `.h:96` `is_safe_to_substitute(var, assertion_start_index)` | on | A substitution is only applied where it is sound with respect to the incremental assertion level it was derived at. | `[C]`/`[I]` |
| **AIG-score-gated normalization** | `src/preprocess/pass/normalize.cpp:48` (class `AigScore`), decision loop at `:1293-1360` | on | Runs normalization **twice** (pass1, pass2), partially bit-blasts original and both results, counts AND gates, and keeps a normalized form only if its AIG is *strictly smaller*. See §1.4. | `[C]` |
| Occurrence counting for `bvmul` / `bvadd` chains | `normalize.cpp:259` / `:315` | on | Flattens a multiply/add DAG into a leaf→multiplicity map, propagating the top node's occurrence down to leaves in descending-ID order so parents finish before children. | `[C]` |
| Common-subterm factoring | `normalize.cpp:386` (`compute_common_subterms`) | on | Factors the greatest common leaf multiset out of the two sides of an (in)equality to maximize sharing; the worked example in the comment turns `{a:6,b:3,c:2,d:1}` vs `{a:7,b:5,c:3}` into a shared `(aaabc * (aaabc * ab))`. | `[C]` |
| Exponent-descending / shift-width sorting | `normalize.cpp:572`, `:579` | on | Deterministic ordering of the normalized product so equal terms hash equal. | `[C]` |
| Square detection in normalization | `normalize.cpp:605` ("square first element"), scoring note at `:183` | on | Recognizes `x*x` and both scores and encodes it with the cheaper squarer circuit. | `[C]` |
| **SAT-solver preprocessing used as an SMT pass** | `src/preprocess/pass/skeleton_preproc.cpp:133-168` | on | Builds a fresh `sat::Cadical`, attaches a `CaDiCaL::FixedAssignmentListener`, encodes the Boolean skeleton, calls `solver()->simplify()`, and lifts every literal CaDiCaL fixed at root level back into a term-level assertion `(= assertion true)`. Bitwuzla is buying CaDiCaL's entire inprocessing suite as a term-level pass. | `[C]` |
| Alpha-equivalence merging of quantifiers | `src/preprocess/pass/quant.cpp:27`, caches at `:37-38` | on (`--pp-quant-alpha`) | Canonicalizes bound-variable names so alpha-equivalent quantifiers become the same node. | `[C]` |

## 1.4 The AIG-score idea, stated precisely

`PassNormalize::apply` does not trust its own rewrite. It builds three
`AigScore` objects — original, normalization pass 1, normalization pass 2 — adds
only the assertions that actually differ, then runs all three **incrementally in
lockstep** (`normalize.cpp:1320-1345`), stopping the moment one candidate is
known to beat the original. `AigScore::process` bit-blasts in chunks with a
default budget of `limit = 100000` new AND gates
(`normalize.cpp:62`, check at `:99`), and `score()` is simply
`d_bitblaster.num_aig_ands()` (`:64`).

Two deliberate approximations are documented in the comments:

- Equality is **abstracted as a Boolean constant** rather than blasted
  (`normalize.cpp:165`).
- `UDIV` and `UREM` are **excluded from the score entirely**, "since bit-blasting
  them is expensive and the preprocessing pass does not normalize these
  operators" (`normalize.cpp:230-232`).

So the estimator is a partial, budgeted, deliberately-lossy bit-blaster used
purely as a cost model, and it decides accept/reject rather than a heuristic on
term size.

## 1.5 The AIG layer

Files: `src/lib/bitblast/bitblaster.h` (operator → bit encodings, backend
agnostic), `src/lib/bitblast/aig/aig_manager.{h,cpp}` (the AIG),
`src/lib/bitblast/aig/aig_cnf.{h,cpp}` (AIG → CNF),
`src/lib/bitblast/aig/aig_printer.cpp` (AIGER export),
`src/solver/bv/aig_bitblaster.{h,cpp}` (the SMT-facing wrapper).

| Name | File:line | Default | What it does | Prov |
| --- | --- | --- | --- | --- |
| Structural hashing (unique table) | `src/lib/bitblast/aig/aig_manager.cpp:19-124` | n/a, always | Power-of-two bucket table with collision chains, doubling `resize()` and rehash; `find_or_create_and` at `:160`. | `[C]` |
| Two-level AND rewriting on construction | `src/lib/bitblast/aig/aig_manager.cpp:178` (`rewrite_and`) | n/a, always | Seven named rule families applied at every `mk_and`, so the AIG is never built naively. | `[C]` |
| — Neutrality (`a ∧ 1 → a`) | `aig_manager.cpp:188` | always | | `[C]` |
| — Idempotence (three variants) | `aig_manager.cpp:192`, `:277`, `:378` | always | Symmetric, asymmetric-with-`(a∧b)∧c`, and a third at `:378`. | `[C]` |
| — Boundedness (`a ∧ 0 → 0`) | `aig_manager.cpp:204` | always | | `[C]` |
| — Contradiction (plain, asymmetric, symmetric) | `aig_manager.cpp:208`, `:226`, `:239` | always | Detects `a ∧ ¬a` through one and two levels of AND nodes. | `[C]` |
| — Subsumption (asymmetric, symmetric) | `aig_manager.cpp:249`, `:262` | always | `¬(a∧b) ∧ c → c` when `a=¬c ∨ b=¬c`, and the two-sided form. | `[C]` |
| — Resolution | `aig_manager.cpp:290` | always | `¬(a∧b) ∧ ¬(c∧d) → ¬a` when `a=d ∧ b=¬c`. | `[C]` |
| — Substitution (asymmetric, symmetric) | `aig_manager.cpp:308`, `:341` (approx.) | always | `¬(a∧b) ∧ c → ¬a ∧ c` when `b=c`. | `[C]` |
| **ITE extraction at CNF time** | `src/lib/bitblast/aig/aig_cnf.cpp:171` (`is_ite`) | n/a, always | Recognizes the four commutative forms of `¬(c∧¬a) ∧ ¬(¬c∧¬b)` and emits a compact ITE clause set instead of two Tseitin ANDs. | `[C]` |
| **Sharing-preserving guard on ITE extraction** | `aig_cnf.cpp:182-197` | always | Refuses the extraction when either inner AND has `parents() > 1` — "Do not extract ITE if it destroys sharing". A parent count is maintained on AIG nodes for exactly this. | `[C]` |
| Top-level / level-aware encoding | `aig_cnf.cpp:39` (`encode(node, top_level, level)`) | always | Encodes a top-level AIG as units rather than as an equivalence, and takes a level for scope. | `[C]` |
| Encoded-flag push/pop | `aig_cnf.cpp:130-149` | always | Pop un-encodes by negating the stored CNF literal in place (`d_aig_encoded[pos] *= -1`) rather than rebuilding. | `[C]` |
| Operand normalization before add/mul | `bitblaster.h:334-351` | always | Sorts operands (`if (a > b) swap`) "s.t. operands with fixed bits come first", making the circuit deterministic and letting constant folding fire earlier. | `[C]` |
| Ripple-carry adder | `bitblaster.h:~421` (`add_helper`) | always | Half adder on the LSB, full adders up the chain. Not a carry-save or parallel-prefix adder. | `[C]` |
| Shift-and-add multiplier with two skips | `bitblaster.h:~436` (`mul_helper`) | always | Skips the whole partial-product row when `b_bit` is the constant false, and skips the full-adder construction when `a[ia]` and the carry are both false. | `[C]` |
| **Dedicated squarer circuit** | `bitblaster.h:370` (`bv_mul_square`) | always, when `x*x` recognized | A distinct, smaller encoding for `a*a` that exploits the symmetry of the partial-product matrix (`n = (size+1)/2` rows instead of `size`). | `[C]` |
| Barrel shifters with overflow guard | `bitblaster.h:126` (`bv_shl`), `:169` (`bv_shr`), `:212` (`bv_ashr`) | always | Log-depth shift, wrapped in an ITE against `ult(b, size)` for the out-of-range case. | `[C]` |
| Restoring divider shared between udiv/urem | `bitblaster.h:354-366` (`udiv_urem_helper`) | always | One circuit yields both quotient and remainder; the two operators are projections of the same call. | `[C]` |
| Sign-aware `bv_slt` reduction | `bitblaster.h:302` | always | Splits on the sign bits and reuses `ult_helper` on the remainder — one `ult` circuit, not two. | `[C]` |
| AIGER export | `src/lib/bitblast/aig/aig_printer.cpp` (228 lines) | via `--write-aiger` (default `""`) | Writes the current BV abstraction as AIGER; a debugging/handoff surface, not part of solving. | `[C]` |
| CNF export | `--write-cnf` (`src/option/option.cpp:285`) | default `""` | Same, in DIMACS. | `[C]` |

## 1.6 The abstraction module (CEGAR over bit-blasting)

Paper: Niemetz, Preiner, Biere — *Bit-Blasting with Abstractions*, CAV 2024
(`NEWS.md:202-207`). Enabled by default since 0.8.0 with `--abstraction-bv-size 33`
(`NEWS.md:131-133`).

The loop: an abstracted term `t = op(x,s)` is replaced by a fresh variable
constrained only by a growing set of **lemma schemas**; when the SAT model
violates the real semantics, violated schemas are added as refinements; if
schemas run out, the term is finally bit-blasted for real.

| Name | File:line | Default | What it does | Prov |
| --- | --- | --- | --- | --- |
| Abstraction module | `src/solver/abstract/abstraction_module.cpp:109` (`check`) | `--abstraction`, **on** (`option.cpp:364`) | The CEGAR driver. | `[C]` |
| Size threshold | `abstraction_module.cpp:300` (`abstract`), option `option.cpp:369` | **33 bits** | Only terms of BV width ≥ 33 are abstracted. | `[C]` |
| `bvmul` abstraction, 19 schemas + value | `abstraction_lemmas.h:26-45`, registered `abstraction_module.cpp:54` | `--abstraction-bvmul`, **on** | `MUL1_POW2`..`MUL19`, `MUL_VALUE`. | `[C]` |
| `bvudiv` abstraction, 37 schemas + value | `abstraction_lemmas.h:47-84`, registered `:60` | `--abstraction-bvudiv`, **on** | `UDIV1_POW2`, `UDIV37` (out of numeric order — it is `s=1 ⇒ t=x`), `UDIV2`..`UDIV36`, `UDIV_VALUE`. | `[C]` |
| `bvurem` abstraction, 15 schemas + value | `abstraction_lemmas.h:86-102`, registered `:66` | `--abstraction-bvurem`, **on** | `UREM1_POW2`..`UREM15`, `UREM_VALUE`. | `[C]` |
| `bvadd` abstraction, 13 schemas + value | `abstraction_lemmas.h:104-118`, registered `:79` | `--abstraction-bvadd`, **off** | Includes overflow/no-overflow sign lemmas (`ADD_OVFL`, `ADD_NOOVFL`) and `ADD_OR` (`x∧s=0 ⇒ t = x∨s`). | `[C]` |
| ITE abstraction | `abstraction_module.cpp:495` (`check_term_abstraction_ite`), kinds `ITE_EXPAND`/`ITE_REFINE` | `--abstraction-ite`, **off** | | `[C]` |
| Assertion abstraction | `abstraction_module.cpp:540` (`check_assertion_abstractions`) | `--abstraction-assert`, **off**, ≤100 refinements/check | Abstracts whole assertions, not just terms. | `[C]` |
| "Initial lemmas only" mode | `abstraction_module.cpp:50` (`opt_initial_lemmas`), consumed by `mk_lemmas` | `--abstraction-initial-lemmas`, **off** | Registers only the starred schemas (`MUL1`..`MUL4`, `UDIV1`..`UDIV6`, `UREM1`..`UREM7`) — the ones the CAV paper marks `*` — and drops the mined tail. | `[C]` |
| Value instantiation | `abstraction_module.cpp:394-420` | on unless `--abstraction-value-only` | Instantiates the schema at the current model values; the limit is `bv_size / 8` per term (`--abstraction-value-limit 8`, `option.cpp:382`), after which the term is bit-blasted. | `[C]` |
| Value-only mode | `abstraction_module.cpp:394` | `--abstraction-value-only`, **off** | Skips symbolic schemas entirely. | `[C]` |
| Eager refinement | `abstraction_module.cpp:406` | `--abstraction-eager-refine`, **off** | Adds *all* violated lemmas at once instead of one. | `[C]` |
| **Square-aware final bit-blast** | `abstraction_module.cpp:461-474` | on | If every value instantiation seen for a `BV_MUL` was a square (`x = s`), the final refinement uses `BITBLAST_BV_MUL_SQUARE` instead of the full multiplier — and resets the counter so the *next* refinement does the full blast. A per-term learned choice of circuit. | `[C]` |
| Incremental bit-blasting of the abstracted term | `abstraction_module.cpp:440`, kind `BITBLAST_INC` | `--abstraction-inc-bitblast`, **off** | Blast `bvmul`/`bvadd` bit-slice by bit-slice rather than all at once. | `[C]` |
| **Offline lemma-schema scorer** | `src/solver/abstract/abstraction_lemma_scorer.{h,cpp}` (352 + 97 lines) | developer tool, not in the solve path | See below — the most transferable idea in this module. | `[C]` |

### The lemma scorer deserves its own paragraph

`AbstractionLemmaScorer` (`abstraction_lemma_scorer.h:31`) is not part of
solving. It is a **build-time mining and validation harness** for the lemma
database, with four entry points:

- `score_lemmas(bv_size)` — how much of the model space each schema excludes.
- `rank_lemmas_by_score(bv_size)` — rank by that.
- `rank_lemmas_by_circuit_size(bv_size, circuit_bv_size)` — rank by the AIG size
  of the schema itself, so a schema that costs more to encode than it saves is
  visible.
- `verify_lemmas(bv_size)` — **check that each schema is actually implied by the
  operator's semantics** at a small width. The schemas are candidate lemmas
  that must be proved before they ship.

And the payoff line, `abstraction_lemma_scorer.h:87`:
`/** Print given ranking as C++ map, to be copied into the source code. */`

The ordering of `MUL5`..`MUL19` and `UDIV7`..`UDIV36` in the shipping enum is a
*generated artifact* pasted back into the source. The un-starred schemas are
mined, scored, verified, ranked offline, and frozen. The `*` in the header
comments marks the hand-derived (invertibility-condition) ones; everything after
is machine-found.

### The published cost, recorded as reported

The prior reading — 80% of solved benchmarks never bit-blast the abstracted
term, at a cost of 13 QF_BV instances and 33% more time — is consistent with the
module being on by default with a conservative 33-bit threshold and a value-
instantiation limit. **I did not verify these numbers**; no measurement was run
and the shallow clone carries no benchmark data. Recorded as `[P]` from the CAV
2024 paper via the brief.

## 1.7 The local-search engine (`src/lib/ls/`)

Propagation-based local search, per Niemetz/Preiner. 9,065 lines across
`ls.cpp` (812), `ls_bv.cpp` (426), `bv/bitvector_node.cpp` (6,336),
`node/node.cpp` (253). Selected by `--bv-solver=prop` or `preprop`
(`option.cpp:238-245`); the default engine is `bitblast`.

| Name | File:line | Default | What it does | Prov |
| --- | --- | --- | --- | --- |
| Propagation-based move selection | `src/lib/ls/ls.cpp:343` (`select_move`) | n/a (engine) | Walks from an unsatisfied root down to a leaf, computing a target value at each step. | `[C]` |
| Essential-input path selection | `ls.cpp:404-430`, option `option.cpp:312` | `--prop-path-sel=essential` | Prefers an input whose change can actually change the node's value; the header comment at `ls.h:136-152` explains the completeness hazard that forces an occasional random pick. | `[C]` |
| Random-input escape probability | `option.cpp:329` | **10/1000** | Probability of taking a random input instead of an essential one, "for completeness (to avoid" getting stuck). | `[C]` |
| **Inverse vs consistent value choice** | `ls.cpp:439-465` | `--prop-prob-pick-inv-value` **990/1000** (`option.cpp:320`) | The documented four-case policy: (0) if all but one input is constant and an inverse exists, take the inverse; (1) else choose inverse-over-consistent by probability; (2) fall back to consistent if no inverse; (3) fall back to inverse if no consistent. | `[C]` |
| Per-operator invertibility conditions | `src/lib/ls/bv/bitvector_node.cpp` — `is_invertible`/`inverse_value` pairs at `:575`/`:645` (add), `:715`/`:847` (and), `:902`/`:999` (concat), `:1057`/`:1174` (eq), `:1243`/`:1587` (mul), `:1645`/`:1995` (shl), `:2053`/`:2310` (shr), `:2507`/`:2770` (ashr), `:2828`/`:3348` (udiv), `:3527` (ult) | always | A closed-form invertibility test and inverse-value computation per operator per argument position. This is the bulk of the 6,336 lines. | `[C]` |
| Per-operator consistent values | same file, `is_consistent`/`consistent_value` pairs at `:607`/`:661`, `:811`/`:863`, `:956`/`:1016`, `:1138`/`:1190`, `:1436`/`:1604`, `:1848`/`:2012`, `:2163`/`:2466`, `:2585`/`:2787`, `:3092`/`:3365` | always | The weaker fallback when no inverse exists. `BitVectorUdiv` has a dedicated `consistent_value_pos0_aux` at `:3378`. | `[C]` |
| Constant-bits propagation | `src/solver/bv/bv_prop_solver.cpp:64`, `fix_bit` at `ls_bv.cpp:96`, domains at `:89` | `--prop-const-bits`, **on** | Maintains a three-valued domain per bit and refuses moves that contradict fixed bits. | `[C]` |
| **Inequality bound inference** | `ls_bv.cpp:270` (`update_bounds_aux`), `:367` (`compute_bounds`), normalization at `bitvector_node.cpp:339`/`:515` | `--prop-ineq-bounds`, **on** | Derives signed and unsigned interval bounds from the `ult`/`slt` roots that a node feeds, intersects them with the target, and restricts inverse-value computation to the surviving range. Bounds are *normalized* (`normalize_bounds`, `compute_normalized_bounds`) so signed and unsigned reasoning share machinery. Per-kind statistics (`num_sbounds_per_kind`, `num_ubounds_per_kind`, `ls_bv.cpp:410`, `:415`). | `[C]` |
| Sign-extend recognition | `option.cpp:356` | `--prop-sext`, **on** | Treats a concat that encodes a sign extension as a `sign_extend` node so the sign-extend-specific inverse rules apply. | `[C]` |
| Cone-of-influence update | `ls.cpp:590` (`update_cone`), timed | always | After a leaf assignment changes, only the affected cone is re-evaluated; the update count is a first-class budget (`--prop-nupdates`). | `[C]` |
| Two independent budgets | `option.cpp:296` (`--prop-nprops`), `:304` (`--prop-nupdates`); both default `0` = unlimited | see `preprop` | Propagation steps and model-value updates are counted and bounded separately. | `[C]` |
| **`preprop` portfolio-in-sequence** | `src/solver/bv/bv_solver.cpp:138`, budget defaults `src/option/option.cpp:981-990` | `--bv-solver=preprop` | Runs local search first with `nprops=10000` and `nupdates=2000000`, then falls back to bit-blasting. The two budgets are set *only if the user did not set them* (`d_is_user_set` guard). | `[C]` |
| Incremental budget carry-over | `bv_prop_solver.cpp:85-97` | on | In incremental mode the limit is *increased by* the configured amount each call rather than reset, so a long session gets a growing local-search allowance. | `[C]` |
| Random restart from unsatisfied root | `ls.cpp:729-742` | always | Picks a random unsatisfied root from a set when the assignment is inconsistent. | `[C]` |
| Backtrackable LS state | `bv_prop_solver.cpp:37` (`d_ls_backtrack`), `ls.h:247-249` (`push`/`pop`) | always | The local searcher itself supports push/pop, so it survives incremental scopes. | `[C]` |

## 1.8 Rewriter levels and rule inventory

`Rewriter` (`src/rewrite/rewriter.h:46`) has **three** levels, only two of which
are user-reachable:

| Level | Constant | Reachable? | Meaning |
| --- | --- | --- | --- |
| 0 | — | `--rewrite-level 0` | All rewrites off **except operator elimination**. |
| 1 | — | `--rewrite-level 1` | One-level (local, structural) rewrites. |
| 2 | `LEVEL_MAX = 2` (`rewriter.h:55`) | `--rewrite-level 2`, **the default** (`option.cpp:287`) | Multi-level rewrites; the header calls these "safe" — non-size-increasing, or size-increasing but "in general always effective in practice". |
| 3 | `LEVEL_ARITHMETIC = LEVEL_MAX + 1` (`rewriter.h:61`) | **not configurable from outside** | "Speculative" rewrites, applied *only* by the normalization pass. Guarded by `d_arithmetic` (`rewriter.cpp:83`, uses at `:1218`, `:1296`, `:1329`, `:1351`, `:1360`, `:1370`, `:1396`, `:1417`). |

A hidden fourth level whose rules are only trusted behind an AIG-size check is
the interesting structural point: **speculative rewrites exist but are quarantined
behind a cost model** rather than either shipped or deleted.

| Family | Where | Count | Prov |
| --- | --- | --- | --- |
| Total named rewrite rules | `enum class RewriteRuleKind`, `src/rewrite/rewriter.h:372-829` | **296** distinct kinds | `[C]` |
| Boolean | `src/rewrite/rewrites_bool.cpp` (723 lines) | `AND_*` 16, `OR_*` 2, `NOT_*` 4, `XOR_*` 2, `IMPLIES_*` 2 | `[C]` |
| Core (eq / ite / distinct / apply / lambda / quantifier) | `src/rewrite/rewrites_core.cpp` (1844 lines) | `EQUAL_*` 22, `ITE_*` 13, `DISTINCT_*` 4 | `[C]` |
| Bit-vector | `src/rewrite/rewrites_bv.cpp` (4376 lines) | `BV_AND_*` 17, `BV_ADD_*` 13, `BV_MUL_*` 11, `BV_EXTRACT_*` 10, `BV_SLT_*` 7, `BV_ULT_*` 6, `BV_UDIV_*` 6, `BV_XOR_*` 5, `BV_SHR_*` 5, plus ~2 each for 30 further operators | `[C]` |
| **BV normalization (speculative)** | `src/rewrite/rewrites_bv_norm.cpp` (428 lines) | 13 rules: `NORM_BV_ADD_MUL` (`:48`), `NORM_BV_CONCAT_BV_NOT` (`:61`), `NORM_BV_ADD_CONCAT` (`:115`), `NORM_BV_NOT_OR_SHL` (`:132`), `NORM_BV_SHL_NEG` (`:164`), `NORM_BV_EXTRACT_ADD_MUL_REV1/2/3` (`:223`/`:232`/`:241`), `NORM_BV_MUL_POW2_REV` (`:250`), `NORM_FACT_BV_ADD_MUL` (`:275`), `NORM_FACT_BV_ADD_SHL` (`:342`), `NORM_FACT_BV_SHL_MUL` (`:388`), `NORM_FACT_BV_MUL_SHL` (`:408`) | `[C]` |
| Floating-point | `src/rewrite/rewrites_fp.cpp` (822 lines) | `FP_IS_*` 12, `FP_TO_*` 5, `FP_REM_*` 4, plus 2 each for abs/neg/min/max/lt/leq | `[C]` |
| Array | `src/rewrite/rewrites_array.cpp` (56 lines) | small; array reasoning is lemma-based, not rewrite-based | `[C]` |
| Operator elimination | `src/rewrite/rewriter.cpp:1566-1602` | **39 operators eliminated**, 2 deliberately not (`bv_xor`, `bv_comp`) | `[C]` |

The `NORM_*` and `NORM_FACT_*` rules are the ones marked "reverse" and
"factoring" — they *increase* term size in the hope that the AIG shrinks. Four of
the thirteen (`NORM_FACT_*`) are pure factoring. These are the rules that only
exist because there is an AIG-size referee.

Rewriting details worth noting: `Rewriter::rewrite` (`rewriter.cpp:95`) is an
explicit-stack DAG rewrite with a node cache and a **node-growth warning**
(`rewriter.cpp:128`, `--dbg-rw-node-thresh`) that fires when a single rewrite
introduces more than a configured number of nodes. `Rewriter::eval`
(`rewriter.cpp:145`) is a separate constant-folding entry that requires all
leaves to be values.

## 1.9 SAT-layer integration and everything else

| Name | File:line | Default | What it does | Prov |
| --- | --- | --- | --- | --- |
| Backend SAT solvers | `src/sat/` — `cadical.cpp`, `kissat.cpp`, `cryptominisat.cpp`, `gimsatul.cpp` | **CaDiCaL** when available (`option.cpp:246-249`) | Four backends behind one `SatSolver` interface. | `[C]` |
| **`ilb` forced on** | `src/sat/cadical.cpp:46` — `d_solver->set("ilb", 2)` with comment "Useful for incremental" | always | Bitwuzla overrides one CaDiCaL option unconditionally. Whatever `ilb` defaults to in CaDiCaL, Bitwuzla does not use that value. | `[C]` |
| **Activation-variable push/pop** | `src/sat/cadical.cpp:73-77` (append activation literal to each clause), `:141-147` (assume all activations negatively), `:159-171` (pop makes the activation literal a permanent unit) | always, since HEAD | Replaces clause deletion with one activation variable per scope level. `NEWS.md:18-20`: "Improved push/pop support in the SAT backends. Now uses activation variables to remove clauses on pop()." | `[C]`+`[P]` |
| Kissat / Gimsatul incrementality by re-instantiation | `NEWS.md:91-93`, `:97-99` | n/a | Neither supports incremental solving; Bitwuzla builds a fresh solver per query. | `[P]` |
| IPASIR-UP external propagator | `src/sat/propagator.{h,cpp}`, `sat_propagator.h`, connected at `src/sat/cadical.cpp:131-132` | on when a propagator is registered | Also connects a fixed-assignment listener to the same object. | `[C]` |
| **All-different constraint propagator** | `src/sat/distinct_n_propagator.{h,cpp}` | `--adc-sat-propagator`, **off** (`option.cpp:270`); default is theory-level handling | Implements Biere & Brummayer, *Consistency Checking of All Different Constraints over Bit-Vectors within a SAT Solver*, FMCAD'08 — **generalized with a collision threshold**: for `N` bit-vectors and target cardinality `C`, up to `N−C` assignment collisions are tolerated before a conflict clause is emitted, so the same propagator does exact-distinct and cardinality-`C`-distinct. | `[C]`+`[P]` |
| Theory-aware SAT decision heuristics | `src/sat/distinct_decision_heuristic.{h,cpp}`, `src/sat/eq_decision_heuristic.{h,cpp}` (both © 2026) | attached with the propagator | Custom `SatPropagator` subclasses that steer CaDiCaL's decisions using knowledge of which CNF literals form a bit-vector (`d_bvs`, `d_idxmap`, `eq_decision_heuristic.h:35-36`). Decision heuristics injected from the theory side. | `[C]` |
| Bit-level interpolation | `src/interpolator.{h,cpp}`, `src/solver/bv/bv_interpolator.{h,cpp}`, `src/sat/interpolants/{tracer,cadical_tracer,tracer_kinds}.cpp` | `--interpolants-algo=mcmillan` (default) or `pudlak` (`option.cpp:436`) | Niemetz & Preiner, *Bit-Precise Interpolation in Bitwuzla*, TACAS 2026. Full QF_BV support; experimental FP; **partial** array/UF — A/B-mixed lemmas in the SAT proof core raise an exception. | `[C]`+`[P]` |
| Interpolant lifting to the theory level | `--interpolants-lift`, **on** (`option.cpp:441`) | on | Lifts a bit-level AIG interpolant back to BV terms; disabling gives a 1:1 AIG transcription. | `[C]` |
| Interpolant by substitution | `--interpolants-subst`, **off**; `Interpolator::interpolant_by_substitution` (`interpolator.h:76`) | off | A cheaper route when the partition allows it; stats `interpolant_substA`/`substB`/`bitlevel` distinguish which route produced each result. | `[C]` |
| Inductive interpolant sequences | `Interpolator::get_interpolants` (`interpolator.h:51`) | n/a | Returns `⟨I_1..I_n⟩` with the inductiveness guarantee stated in the header comment. | `[C]` |
| Lemmas-on-demand array solver | `src/solver/array/array_solver.{h,cpp}` — `add_congruence_lemma` (`.h:145`), `add_access_store_lemma` (`.h:155`), `add_access_const_array_lemma` (`.h:164`), `add_const_array_equality_lemma` (`.h:166`), `add_disequality_lemma` (`.h:179`) | on | Five lemma schemas with **path conditions**, plus a `LemmaId` enum (`.h:30`) and per-schema de-duplication caches (`.h:306`, `:308`). | `[C]` |
| Lemmas-on-demand UF solver | `src/solver/fun/fun_solver.{h,cpp}` — `add_function_congruence_lemma` (`.h:41`) | on | Congruence by lemma, not by eager Ackermannization. | `[C]` |
| MBQI quantifier solver | `src/solver/quant/quant_solver.{h,cpp}` — `skolemization_lemma` (`.h:69`), `value_inst_lemma` (`.h:70`), `mbqi_lemma` (`.h:76`) | on | Plus an explicit "too expensive to add as a lemma" filter (`.h:144`). | `[C]` |
| **Invertibility-condition MBQI** | `src/preprocess/pass/quant.h` includes `solver/bv/bv_inverter.h`; `NEWS.md:5-10` | `--quant-ic`, **on** (`option.cpp:~460`) | CEGQI via invertibility conditions (Niemetz et al., CAV 2018). Sub-options: `--quant-ic-bounds` **on**, `--quant-ic-underdet` **on** (under-determined inverses for extract/concat), `--quant-ic-filter` **off** (unfiltered by default — every IC lemma is added), `--quant-ic-value-limit 4`. Same invertibility-condition machinery as the local-search engine, reused for quantifiers. | `[C]`+`[P]` |
| FP via SymFPU word-blasting | `src/solver/fp/` (symfpu wrapper, `word_blaster.cpp`) | on | FP is reduced to BV; SymFPU 1.2.0 (`NEWS.md:25`). | `[C]` |
| Self-checking of every answer class | `src/check/check_model.cpp`, `check_unsat_core.cpp`, `check_interpolant.cpp` | `--dbg-check-model` defaults to `config::is_debug_build` (`option.cpp:~590`) | Independent checkers for model, unsat core, and interpolant, on by default in debug builds only. | `[C]` |
| Unsat-core assertion tracking | `src/preprocess/assertion_tracker.{h,cpp}`, `Preprocessor::post_process_unsat_core` (`preprocessor.h:66`) | on when `--produce-unsat-cores` or `--produce-interpolants` | Maps preprocessed assertions back to original ones; the tracker is allocated only when needed (`preprocessor.cpp:48-49`). | `[C]` |
| External SAT solver factory | `NEWS.md:70-72`; `src/sat/sat_solver_factory.{h,cpp}` | API | `Bitwuzla(TermManager&, SatSolverFactory&, const Options&)` — a supported injection point for a third-party SAT backend. | `[P]`+`[C]` |
| BTOR2 output | `--output-lang` (`NEWS.md:85-87`) | off | QF_BV and QF_ABV only. | `[P]` |

## 1.10 Bitwuzla — what I did not verify

- The CAV 2024 abstraction cost/benefit numbers (80% / −13 instances / +33%
  time). No run; recorded from the brief and the paper.
- The exact line of the truncated comment at `src/option/option.cpp:955-959`
  about assertion abstraction being force-disabled.
- `LEVEL_ARITHMETIC` rule-by-rule behaviour — I confirmed the guard sites and the
  13 `NORM_*` rules, not what each rule does.
- Whether `d_arithmetic` rewrites are reachable through any path other than
  `PassNormalize`. The header says no; I did not exhaustively grep constructors.
- The `quant_ic` option line numbers in `option.cpp` (I read the block but
  recorded an approximate line for `--quant-ic`).
- `src/solver/fp/` beyond its file listing.

---

# 2. Kissat 4.0.4

Paths below are relative to `references/kissat/`. All defaults were read from
the `OPTION(...)` rows in `src/options.h`, never from memory. Four of the most
load-bearing claims in §2.4 were independently re-verified by this lane after
the sweep; they are marked **[re-verified]**.

## 2.1 Search loop, decisions, phases, restarts

| Name | File:line | Default | What it does | Prov |
| --- | --- | --- | --- | --- |
| Main CDCL search loop | `src/search.c:179` | n/a | Strict `else if` chain: propagate → analyze → reduce → mode-switch → restart → reorder → rephase → probe → eliminate → decide. Earlier phases starve later ones within one iteration. | `[C]` |
| Initial preprocessing phase | `src/preprocess.c:29` | on (`preprocess=1`, `preprocessrounds=1`) | Runs a subset of simplifiers before search, to fixpoint or the round cap. | `[C]` |
| Formula classification | `src/classify.c:5` | on (`smallclauses=1e5`, `bigbigfraction=990`) | Tags the formula "small" and "large binary fraction"; gates `jumpreasons` and effort decisions. | `[C]` |
| Focused/stable mode switching | `src/mode.c:186` | on (`stable=1`; 0 = focused only, 2 = stable only) | Alternates VMTF-queue + EMA-restart mode with VSIDS-heap + reluctant-restart mode. | `[C]` |
| **Mode limit alternation (conflicts ↔ ticks)** | `src/mode.c:186` | on (`modeinit=1e3`, `modeint=1e3`) | Odd switches are bounded by *ticks* spent in the previous mode, even ones by *conflicts*. Two different currencies alternating. | `[C]` |
| Lucky-phase probes (early) | `src/lucky.c:307` | on (`lucky=1`, `luckyearly=1`) | Tries all-true, all-false, and forward/backward true/false assignments before preprocessing. | `[C]` |
| Lucky-phase probes (late) | `src/search.c:188` | on (`luckylate=1`) | The same six lucky assignments again *after* preprocessing; also extracts units. | `[C]` |
| Warm-up propagation for phases | `src/warmup.c:9` | on (`warmup=1`) | Decides every variable by its saved phase and propagates *beyond* conflicts, to seed local search. | `[C]` |
| Tumbled variable import order | `src/import.c:58` | on (`tumble=1`) | Imports external variables in interleaved rather than DIMACS order. | `[C]` |
| VSIDS/EVSIDS score heap (stable) | `src/decide.c:32` | on (`decay=50` per mille) | Max-score binary heap; the score increment grows by `1/(1−decay)`. | `[C]` |
| VMTF queue (focused) | `src/decide.c:9`, `src/queue.c:5` | on | Move-to-front doubly-linked list with stamps; the last-enqueued unassigned variable is the decision. | `[C]` |
| Score rescaling | `src/bump.c:28` | n/a | Rescales the heap when max score or increment exceeds `MAX_SCORE`. | `[C]` |
| Queue stamp reassignment | `src/queue.c:22` | n/a | Renumbers VMTF stamps on overflow. | `[C]` |
| Random decisions | `src/decide.c:86` | on in focused, **off in stable** (`randec=1`, `randecfocused=1`, `randecstable=0`) | Bursts of uniformly random decisions; burst length `randeclength(10) × log10(count)`. | `[C]` |
| Random-burst scheduling | `src/decide.c:57` | on (`randecinit=500`, `randecint=500`) | LOGN-scaled conflict interval; fires only at level ≤ 1. | `[C]` |
| Bump analyzed variables | `src/bump.c:103` | on (`bump=1`) | Stable: heap score bump. Focused: radix/quick-sorted move-to-front of the analyzed set. | `[C]` |
| Reason-side bumping | `src/analyze.c:169` | on (`bumpreasons=1`, `bumpreasonslimit=10`, `bumpreasonsrate=10`) | Also bumps literals in the *reasons* of learned-clause literals; skipped when the decision rate is ≥ 10. | `[C]` |
| Adaptive delay for reason-side bumping | `src/kimits.c:168` | on | Exponential back-off (`BUMP_DELAY`, `REDUCE_DELAY`) when the technique keeps failing. | `[C]` |
| **Decision-variable reordering** | `src/reorder.c:198` | on, both modes (`reorder=2`; 1 = stable only) | Recomputes weights `max(pos,neg) + 2·min(pos,neg)` from size-decayed clause occurrences and re-sorts the heap and the queue. A periodic re-seeding of the branching order from structure rather than from conflict history. | `[C]` |
| Reorder weight table | `src/reorder.c:24` | on (`reordermaxsize=100`) | A clause of size *s* contributes `2^−(s−2)`; binaries counted from watch lists. | `[C]` |
| Phase saving | `src/decide.c:168` | on (`phasesaving=1`) | | `[C]` |
| Target phases | `src/decide.c:158` | on in **stable only** (`target=1`; 2 = both, 0 = off) | Phases from the deepest conflict-free trail outrank saved phases. | `[C]` |
| Best phases | `src/phases.c:58`, `src/backtrack.c:38` | n/a | Phases at the largest trail ever reached; consumed by rephasing. | `[C]` |
| Initial phase | `src/decide.c:199` | on (`phase=1` = positive, `forcephase=0`) | Fallback when neither target nor saved phase is set. | `[C]` |
| **Focused-mode phase oscillation** | `src/decide.c:178` | n/a | In focused mode, bits 1 and 3 of the mode-switch count force all-original / all-inverted phases. Rephasing is stable-only, so focused mode gets this instead. | `[C]` |
| Rephasing schedule | `src/rephase.c:86` | on, **stable only** (`rephase=1`, `rephaseinit/int=1e3`) | Cyclic six-step schedule: **best, walking, inverted, best, walking, original**. | `[C]` |
| Rephase interval scaling | `src/rephase.c:119` | n/a | `NLOG3N` — interval grows as `n·log10(n)³` in the rephase count. | `[C]` |
| EMA glue restarts (focused) | `src/restart.c:14` | on (`restart=1`, `restartmargin=10%`) | Restart when `1.10 × slow_glue ≤ fast_glue`; EMA windows 1e5 / 33. | `[C]` |
| Focused restart interval | `src/restart.c:39` | on (`restartint=1`, 50 under `--sat`) | Minimum conflicts between restarts, growing by `log10(restarts)`. | `[C]` |
| Reluctant doubling (Luby) in stable | `src/reluctant.c:20` | on (`reluctant=1`, `reluctantint=1024`, `reluctantlim=2^20`) | The classic `(u & -u) == v` generator, ticked per learned clause, capped and reset at the limit. | `[C]` |
| Trail reuse on restart | `src/restart.c:86` | on (`restartreusetrail=1`) | Keeps the decision prefix whose score/stamp beats the next decision variable. | `[C]` |
| Mode-specific trail-reuse rules | `src/restart.c:53`, `:69` | on | Stable compares heap scores; focused compares VMTF stamps. | `[C]` |

## 2.2 Clause database, arena, conflict analysis

| Name | File:line | Default | What it does | Prov |
| --- | --- | --- | --- | --- |
| Three glue tiers | `src/reduce.c:62`, `src/internal.h:255` | on (`tier1=2`, `tier2=6`) | tier1 kept if recently used; tier2 kept if used ≥ `MAX_USED−1`; tier3 reduced freely. | `[C]` |
| **Dynamic tier recomputation from a glue histogram** | `src/tiers.c:6` | on (`tier1relative=500`, `tier2relative=900` per mille) | Tier boundaries are set to the 50th and 90th glue *percentiles of the clauses actually used*, recomputed per mode. The tiers are measured, not constants. | `[C]` |
| Tier recomputation during analysis | `src/analyze.c:519` | on | Recomputed on a doubling conflict interval up to 2^16. | `[C]` |
| 2-bit clause `used` counter | `src/reduce.c:70`, `src/deduce.c:14` | n/a | Set on participation in conflict analysis, decremented once per reduction. | `[C]` |
| Reduce with dynamic keep fraction | `src/reduce.c:102` | on (`reducelow=500`, `reducehigh=900` per mille) | Deleted fraction interpolates 50% → 90% as `high − (high−low)/log10(reductions+9)`. | `[C]` |
| Reduce ranking (glue then size) | `src/reduce.c:82` | n/a | 64-bit rank `~size \| (~glue << 32)`, radix-sorted. | `[C]` |
| Reduce scheduling | `src/reduce.c:14`, `:193` | on (`reduceinit/int=1e3`) | Conflict interval scaled by `SQRT(reductions)`. | `[C]` |
| Clause promotion on glue improvement | `src/promote.c:5` | on (`promote=1`) | Lowers a redundant clause's glue when re-derived tighter, moving it between tiers. | `[C]` |
| Glue recompute during analysis | `src/deduce.c:29` | on | `kissat_recompute_and_promote` recomputes the LBD of reason clauses seen in analysis. | `[C]` |
| Arena region markers | `src/collect.c:183`, `:198` | n/a | First-reducible / last-irredundant bounds limit the region a reduction must sweep. | `[C]` |
| Redundant relocation to arena end | `src/collect.c:213` | n/a | Keeps irredundant clauses in a contiguous prefix. | `[C]` |
| Compacting garbage collection | `src/collect.c:633`, `src/compact.c:19` | on (`compact=1`, `compactlim=10%`) | Renumbers variables once ≥10% are inactive; remaps queue, heap, trail, frames, phases. | `[C]` |
| Sparse vs dense collection | `src/collect.c:608`, `:728` | n/a | Watch-list sweep during search; occurrence-list sweep during BVE/walk. | `[C]` |
| Arena / "ward" clause allocation | `src/arena.c:25`, `src/arena.h:23` | n/a | One contiguous stack of 32/64-bit wards; clauses referenced by 29-bit offsets. | `[C]` |
| Tagged 32-bit watches | `src/watch.h:18` | n/a | One word per watch: 1 tag bit + 31-bit literal (binary) or reference; large watches use a blocking-literal word plus a reference word. | `[C]` |
| **Watch replacement of true literals** | `src/proplit.h:32` | n/a | On finding a true literal, actually *replaces the watch* rather than only updating the blocking literal (attributed in-source to Manthey). | `[C]`+`[P]` |
| Watch-list defragmentation | `src/vector.c` (`defraglim=75`, `defragsize=2^18`) | on | Compacts the shared watch arena when the usable fraction drops below 75%. | `[C]` |
| 1-UIP conflict analysis | `src/deduce.c:70` | n/a | Trail-walk first-UIP resolution with per-level frame counters. | `[C]` |
| Chronological backtracking | `src/learn.c:16` | on (`chrono=1`, `chronolevels=100`) | Backtracks to `level−1` instead of the jump level when the jump would skip more than 100 levels. | `[C]` |
| Conflict-level repair | `src/analyze.c:16` | n/a | Finds the true conflict level under out-of-order assignments, re-watches, and reuses the conflict as a driving clause when only one literal is on that level. | `[C]` |
| On-the-fly strengthening (OTFS) | `src/deduce.c:98`, `src/strengthen.c:142` | on (`otfs=1`) | When a resolvent is shorter than its antecedent, strengthen the antecedent in place and continue from it. | `[C]` |
| On-the-fly subsumption | `src/strengthen.c:156` | on (via `otfs`) | If the strengthened resolvent also subsumes the original conflict, delete the conflict. | `[C]` |
| Recursive clause minimization | `src/minimize.c:155` | on (`minimize=1`, `minimizedepth=1e3`) | Poison/removable caching with bounded recursion depth. | `[C]` |
| All-UIP clause shrinking | `src/shrink.c:360` | on (`shrink=3`; 1 = binary, 2 = large, 3 = recursive) | Each decision-level block of the learned clause is shrunk to a single UIP, falling back to minimization per block. | `[C]` |
| Ticks charged inside minimize/shrink | `src/minimize.c:51`, `src/shrink.c:179` | on (`minimizeticks=1`) | Minimization work is charged to the same tick budget that drives every effort limit. | `[C]` |
| Eager subsumption of recent learned clauses | `src/learn.c:145` | on (`eagersubsume=4`) | Each new learned clause is checked against the last 4; subsumed ones are deleted. | `[C]` |
| **Binary reason jumping** | `src/fastassign.h:12`, `src/assign.c:38` | on (`jumpreasons=1`) | Replaces a binary reason by *its own* binary reason — but only when the formula was classified "big-binary" (≥99% binaries). A technique gated on a formula classifier. | `[C]` |
| Learned-clause watch selection | `src/learn.c:81` | n/a | The second watch is the highest-level literal; short-circuits at `level−1`. | `[C]` |
| Failed-literal analysis at level 1 | `src/analyze.c:390` | n/a | A conflict at decision level 1 is resolved into a *set of units*, not a clause. | `[C]` |
| Bias-corrected EMAs | `src/smooth.c:25` | on (`emafast=33`, `emaslow=1e5`) | Exponential moving averages with exponential bias correction, for glue, trail, level, decision rate. | `[C]` |

## 2.3 Inprocessing

### Probing round

| Name | File:line | Default | What it does | Prov |
| --- | --- | --- | --- | --- |
| Probing scheduler | `src/probe.c:70` | on (`probe=1`, `probeinit=100`, `probeint=100`, `proberounds=2`) | Up to 2 rounds; conflict interval scaled `NLOGN` *and* U-shaped by formula size. | `[C]` |
| Probing round order | `src/probe.c:26` | n/a | congruence → substitute → backbone → vivify → sweep → substitute → transitive → backbone → factor. Note `substitute` and `backbone` each appear **twice**. | `[C]` |
| **Clausal congruence closure** | `src/congruence.c:4578` | on (`congruence=1`, `congruenceonce=0`) | Extracts gates, hashes their definitions, merges literals whose gate definitions match into equivalence classes. | `[C]` |
| — AND-gate extraction | `src/congruence.c:3865` | on (`congruenceands=1`, `congruenceandarity=1e6`) | Base clause + binary index. | `[C]` |
| — XOR-gate extraction | `src/congruence.c:3904` | on (`congruencexors=1`, `congruencexorarity=4`, `congruencexorcounts=2`) | Full side-clause sets, up to arity 4. | `[C]` |
| — ITE-gate extraction | `src/congruence.c:3943` | on (`congruenceites=1`) | Conditional-equivalence search over ternary clauses; 4.0.4 fixed a quadratic blow-up here. | `[C]`+`[P]` |
| — Binary-clause recovery for gate matching | `src/congruence.c:2226` | on (`congruencebinaries=1`) | Recovers implied binaries from larger clauses so more gates match. | `[C]` |
| — Gate rewriting under merges, with proof chains | `src/congruence.c:2160`, `:1042`, `:1084` | on | Emits DRAT chains for each rewrite step. | `[C]` |
| — Unit + representative propagation fixpoint | `src/congruence.c:4029`, `:4082`, `:4210` | on | | `[C]` |
| — Forward subsumption of newly duplicate clauses | `src/congruence.c:4446` | on | | `[C]` |
| — Adaptive delay | `src/congruence.c:4631` | on | Backs off when <0.1% of variables merge. | `[C]` |
| Equivalent-literal substitution (SCC) | `src/substitute.c:604` | on (`substitute=1`, `substituterounds=2`, `substituteeffort=10` per mille) | Representatives over the binary implication graph, then a global rewrite. | `[C]` |
| Representative determination | `src/substitute.c:38` | on | Union-find-style, with unit extraction. | `[C]` |
| **Binary-clause backbone (restricted failed-literal probing)** | `src/backbone.c:572` | on (`backbone=1`; 2 = eager, `backboneeffort=20` per mille) | Assume a candidate, propagate, learn a unit from a conflict — but only for literals occurring in binary clauses. This is what survives of general failed-literal probing. | `[C]` |
| Backbone round budget | `src/backbone.c:344` | on (`backbonerounds=100`, `backbonemaxrounds=1e3`) | `backbonerounds × #computations`, capped, plus a tick limit. | `[C]` |
| Backbone candidate retention | `src/backbone.c:70` | on | Untried candidates stay flagged for the next probing round. | `[C]` |
| Backbone-specific conflict analysis | `src/backbone.c:261` | on | A dedicated analyzer producing the negated failed literal. | `[C]` |
| **Vivification, four tiers** | `src/vivify.c:1395` | on (`vivify=1`, `vivifyeffort=100` per mille) | One budget subdivided across tier1:tier2:tier3:irredundant in the ratio **3:3:1:3** (`vivify.c:1417-1466`). | `[C]` |
| — tier1 (glue ≤ tier1) | `src/vivify.c:1352` | on (`vivifytier1=3`) | | `[C]` |
| — tier2 (tier1 < glue ≤ tier2) | `src/vivify.c:1362` | on (`vivifytier2=3`) | | `[C]` |
| — tier3 (glue > tier2) | `src/vivify.c:1373` | on (`vivifytier3=1`) | Gets the *smallest* share. | `[C]` |
| — irredundant | `src/vivify.c:1384` | on (`vivifyirr=3`) with adaptive delay | Re-added in 3.1.0; backs off when the success rate falls below 1%. | `[C]`+`[P]` |
| **Vivification instantiation** | `src/vivify.c:1200` | on (part of vivify) | When propagation leaves exactly one implied literal, tries *flipping* it to strengthen the clause. | `[C]` |
| Vivification candidate sorting | `src/vivify.c:231`, `:442` | on (`vivifysort=1`) | Ranks by literal occurrence counts; skips sorting irredundant when the redundant pool is tiny. | `[C]` |
| Vivification candidate carry-over | `src/vivify.c:1300` | on | Unfinished candidates keep their `vivify` bit for the next round. | `[C]` |
| **SAT sweeping (sub-solver congruence)** | `src/sweep.c:1648` | on (`sweep=1`, `sweepeffort=100` per mille) | Builds a bounded environment around each variable, solves it with the embedded *kitten* sub-solver, derives units and equivalences. | `[C]` |
| — Environment growth | `src/sweep.c:725` | on (`sweepvars=256`, `sweepdepth=2`, `sweepclauses=1024`; max `8192`/`3`/`32768`) | Breadth-first cone of influence, limits doubling as sweeps succeed. | `[C]` |
| — Backbone / partition refinement from models | `src/sweep.c:588`, `:500` | on | Every SAT model from the sub-solver refines both the candidate backbone set and the equivalence partition. | `[C]` |
| — Literal flipping instead of a solver call | `src/sweep.c:623`, `:1080` | on (`sweepfliprounds=1`) | `kitten_flip_literal` refutes candidates on a partial model without re-solving. | `[C]` |
| — Core extraction and clause export | `src/sweep.c:311`, `:347` | on | Saves the clausal core of an UNSAT sub-solve so the learned units/equivalences carry a proof. | `[C]` |
| — Rescheduling of incomplete variables | `src/sweep.c:1531`, `:1587` | `sweepcomplete=0` (**off**) | Incomplete variables are deferred; `--sweepcomplete` runs to completion. | `[C]` |
| — Adaptive delay | `src/sweep.c:1714` | on | Backs off below 0.1% yield. | `[C]` |
| Transitive reduction | `src/transitive.c:299` | on (`transitive=1`, `transitiveeffort=20` per mille) | Removes binaries implied by a longer binary path; also derives units. | `[C]` |
| Transitive candidate retention | `src/transitive.c:357` | on (`transitivekeep=1`) | | `[C]` |
| New-binary prioritization | `src/transitive.c:48` | on | Binaries added since the last round are probed first. | `[C]` |
| **Bounded variable addition (factoring)** | `src/factor.c:1087` | on (`factor=1`, `factoreffort=50` per mille, `factorsize=5`) | Finds a common factor literal set across clauses and introduces a fresh extension variable. | `[C]` |
| — Quotient search | `src/factor.c:325`, `:607` | on (`factorcandrounds=2`, `factorhops=3`) | Greedy next-factor selection; best quotient by clause-count gain. | `[C]` |
| — Size-based delay | `src/factor.c:1068` | on (`factordelay=4`) | Skips BVA while `log10(active) > eliminations + 4` — added in 4.0.4 to hold it off on large formulas. | `[C]`+`[P]` |
| — Fixed first budget | `src/factor.c:1105` | on (`factoriniticks=700` million) | The first factorization gets a flat 700M ticks rather than an effort-relative budget. | `[C]` |

### Elimination round

| Name | File:line | Default | What it does | Prov |
| --- | --- | --- | --- | --- |
| Bounded variable elimination | `src/eliminate.c:595` | on (`eliminate=1`, `eliminateeffort=100` per mille) | Dense occurrence lists, resolvent generation, weaken-and-remove. | `[C]` |
| **Growing elimination bound** | `src/eliminate.c:339` | on (`eliminatebound=16`) | The allowed added-clause bound doubles 0→1→2→…→16 each time elimination completes, and **all variables are retried at each new bound**. | `[C]` |
| BVE scheduling by score | `src/eliminate.c:41`, `:131` | on (`eliminateocclim=2e3`) | Min-heap on `branching relevancy + (pos·neg − pos − neg) − occlim²`. | `[C]` |
| BVE clause/occurrence caps | `src/resolve.c:264` | on (`eliminateclslim=100`, `eliminateocclim=2e3`) | Fixed, not dynamically raised. | `[C]`+`[P]` |
| Elimination rounds | `src/eliminate.c:416` | on (`eliminaterounds=2`) | Alternates forward subsumption and elimination. | `[C]` |
| **Gate extraction for BVE, ordered** | `src/gates.c:34` | on (`extract=1`) | equivalence → AND(lit) → AND(¬lit) → ITE(lit) → ITE(¬lit) → general definition. First match wins. | `[C]` |
| — Equivalence gates | `src/equivalences.c:5` | on (`equivalences=1`) | `x ↔ y` from two binaries. | `[C]` |
| — AND gates | `src/ands.c:6` | on (`ands=1`) | `x ↔ (a ∧ b ∧ …)` by marking binaries and matching a long clause. | `[C]` |
| — ITE gates | `src/ifthenelse.c:95` | on (`ifthenelse=1`) | Four ternary clauses forming `x ↔ (c ? t : e)`. | `[C]` |
| **— General definition extraction via a sub-solver** | `src/definition.c:91` | on (`definitions=1`, `definitionticks=1e6`, `definitioncores=2`) | Feeds both occurrence lists to kitten; an UNSAT answer *proves a definition exists* and the clausal core **is** the gate. No syntactic pattern needed. | `[C]` |
| — Repeated core shrinking | `src/definition.c:143` | on (`definitioncores=2`) | Shrink to the core, shuffle, re-solve with 10× ticks to obtain a smaller core. | `[C]` |
| — One-sided core → failed literal | `src/definition.c:198` | on | When one side of the core is empty, the attempt yields a unit instead of a gate. | `[C]` |
| Elimination by substitution | `src/resolve.c:340` | on (via `extract`) | With a gate present, only gate × non-gate resolvents are generated, not all pairs. | `[C]` |
| Pure-literal elimination | `src/resolve.c:290` | on | A literal with zero occurrences on one side is eliminated for free. | `[C]` |
| Forward subsumption + strengthening | `src/forward.c:678` | on (`forward=1`, `forwardeffort=100` per mille, `subsumeclslim=1e3`, `subsumeocclim=1e3`) | Runs inside each BVE round. | `[C]` |
| Duplicate binary removal | `src/forward.c:13` | on | While walking watch lists. | `[C]` |
| **Duplicate hyper-unary resolution** | `src/forward.c:42` | on | If both `(l ∨ o)` and `(l ∨ ¬o)` exist, derive the unit `l`. This is the *only* surviving "hyper" resolution in Kissat. | `[C]` |
| Fast variable elimination | `src/fastel.c:822` | **off** (`fastel=0`) — see §2.4 | Cheap occurrence-list BVE with tight limits (`fastelim=8`, `fasteloccs=100`, `fastelrounds=4`, `fastelclslim=100`, `fastelsub=1`). | `[C]` |
| Weakening / extension stack | `src/weaken.c:36` | n/a | Every eliminated clause is pushed with its witness literal. | `[C]` |
| Model extension | `src/extend.c:44` | n/a | Replays the extension stack backwards. | `[C]` |
| Dense ↔ sparse mode switching | `src/dense.c:99`, `:199` | n/a | Converts watch lists to full occurrence lists for BVE/walking and back. | `[C]` |

### Local search, propagation variants, proofs, sub-solver

| Name | File:line | Default | What it does | Prov |
| --- | --- | --- | --- | --- |
| WalkSAT-style local search | `src/walk.c:936` | on, **reachable only via rephasing** (`walkeffort=50` per mille) | ProbSAT break-value scoring; imports the current decision phases as its start assignment. | `[C]` |
| Break-value score table | `src/walk.c:146`, `:164` | on | Piecewise-linear `cb` per average clause size (2.00 … 2.85 …) driving an exponential score table. | `[C]` |
| Best-assignment export | `src/walk.c:784`, `:793` | on | The best local-search assignment becomes the new saved phases. | `[C]` |
| Walk trail / implied-literal flipping | `src/walk.c:624`, `:664` | on | Keeps a trail of forced literals so flips propagate. | `[C]` |
| Search propagation | `src/propsearch.c:44` | n/a | Two-watched-literal with blocking literals and delayed large-watch pushes. | `[C]` |
| Probing propagation | `src/proprobe.c:35` | n/a | Same core with an "ignore" clause and probing tick accounting. | `[C]` |
| **Propagation beyond conflicts** | `src/propbeyond.c:34` | n/a | Does not stop at the first conflict — a separate propagator written for warm-up. | `[C]` |
| Dense propagation | `src/propdense.c:86` | n/a | Occurrence-list propagation while in dense (BVE) mode. | `[C]` |
| Initial propagation | `src/propinitially.c:34` | n/a | Root-level, before preprocessing. | `[C]` |
| DRAT proof output | `src/proof.c:54` | on with `-o` (`flushproof=0`) | Binary DRAT to files, ASCII to stdout. | `[C]` |
| Internal RUP+RAT checker | `src/check.c:150`, `:787` | debug builds only (`check=2`) | Independent bucket-hashed checker for every derived clause, including a blocked-literal (RAT) test. | `[C]` |
| Model checking | `src/check.c:17` | debug builds (`check=1`) | Evaluates the extended model against all original clauses. | `[C]` |
| Simplified-formula DIMACS output | `src/krite.c:8` | via `-o <file>` | Writes the preprocessed formula; new in 4.0.0. | `[C]`+`[P]` |
| Partial witness printing | `src/witness.c:27` | via `--partial` | Prints only assigned variables. | `[C]` |
| **Kitten CDCL sub-solver** | `src/kitten.c` (2877 lines), API `src/kitten.h:10` | n/a | A small self-contained CDCL used by definition extraction and by sweeping. A second, cheaper solver *inside* the solver. | `[C]` |
| — Antecedent tracking / clausal core | `src/kitten.h:14`, `:41` | n/a | `kitten_track_antecedents`, `kitten_compute_clausal_core`, `kitten_shrink_to_clausal_core`. | `[C]` |
| — Literal flipping | `src/kitten.h:38` | n/a | Tests whether a literal can be flipped in the current model without breaking a clause. | `[C]` |
| — Clause shuffling / phase randomization | `src/kitten.h:16` | n/a | Used to obtain a *different*, smaller core on re-solve. | `[C]` |
| **Tick-based effort budgets** | `src/kimits.h:135` | on (`mineffort=10` million) | Every simplifier receives `effort_per_mille × (search ticks since it last ran)`, floored at 10M. | `[C]` |
| U-shaped interval scaling by formula size | `src/kimits.c:39` | on | `delta × (4.5·(log10(C)−5)² + 25)`; new in 4.0.0. Both very small and very large formulas get simplified more often. | `[C]`+`[P]` |
| Shared adaptive-delay counters | `src/kimits.c:155` | on | One back-off mechanism reused by congruence, sweep, vivify-irredundant, reason bumping. | `[C]` |
| **Cache-line tick accounting** | `src/proplit.h:66` | n/a | Ticks are charged as *cache lines touched*, not literals visited — the effort unit is deliberately machine-independent. | `[C]` |

## 2.4 Kissat — removed, default-off, and dead

### Default-off options

| Option | `src/options.h` | Note |
| --- | --- | --- |
| `fastel=0` | `:62` | **[re-verified]** Fast preprocessing BVE. Disabled by default in 4.0.4; the whole 934-line `fastel.c` is unreachable in a default run. |
| `walkinitially=0` | `:169` | **[re-verified] A dead option.** `grep -rn walkinitially references/kissat/src references/kissat/test` returns hits *only* in `options.h:169`, `test/testusage.c:54,56`, `test/testsolve.c:30` and one cover CNF. No source file outside the option table reads it. Setting it changes nothing, and the tests that pass it therefore assert nothing about it. |
| `randecstable=0` | `:108` | Random decisions in stable mode. |
| `congruenceonce=0` | `:30` | Restrict congruence closure to preprocessing only. |
| `sweepcomplete=0` | `:141` | Run SAT sweeping to completion. |
| `sweeprand=0` | `:148` | Randomized sweeping environment. |
| `factorstructural=0` | `:61` | Structural (hop-based, `factorhops=3`) BVA scoring; the default uses watch-count scoring. |
| `forcephase=0` | `:70` | Ignore target and saved phases. |
| `incremental=0` | `:74` | `kissat_solve` (`src/internal.c:475`) hard-refuses a second call: `kissat_require (!GET (searches), "incremental solving not supported")`. |
| `flushproof=0` | `:68` | |

`--plain` (`src/config.c:39`) turns off bumpreasons, chrono, compact,
eagersubsume, jumpreasons, otfs, preprocess, reorder, rephase,
restartreusetrail, simplify, tumble, and forces stable-only. `--basic`
additionally kills restart, reduce, minimize. Useful as a named ablation
baseline.

### Compiled out

**`focusedtiers` is dead code, and the live macro is asymmetric. [re-verified]**
`src/internal.h:250-257` reads:

```c
#if 0
#define TIEDX (GET_OPTION (focusedtiers) ? 0 : solver->stable)
#define TIER1 (solver->tier1[TIEDX])
#define TIER2 (solver->tier2[TIEDX])
#else
#define TIER1 (solver->tier1[0])
#define TIER2 (solver->tier2[1])
#endif
```

The option `focusedtiers` (default 1) is read by nothing. What actually ships is
**`tier1` always read from index 0 (focused) and `tier2` always from index 1
(stable)** — the two tier boundaries are taken from *different modes' histograms*
regardless of which mode is running. The option's own description ("always used
focused mode tiers") does not describe the code. Source wins; recorded as a
disagreement, not resolved.

### Verified absent from `src/`

Each of these was removed (per `NEWS.md`, "Version sc2022-light") and confirmed
absent by grep in 4.0.4:

- **Autarky reasoning** — zero hits for `autark`.
- **Hyper binary resolution** — absent. Removing it freed a literal-encoding bit
  (virtual binaries in watch lists no longer need a provenance bit), which raised
  the variable ceiling from 2^28−1 to 2^29−1 and later past a billion (NEWS 3.1.0).
  The brief's note that HBR "was partly reinstated as useful for UNSAT" is **not
  visible in 4.0.4** — what exists is *hyper-unary* resolution at `src/forward.c:42`,
  a different technique. Recorded as a disagreement between the brief's prior and
  the source; source wins.
- **Hyper ternary resolution** — absent; no ternary statistics counters.
- **CHB and ACIDS branching** — added in sc2022-bulky (off by default), now gone.
- **Gaussian elimination / XOR reasoning over the CNF** — absent. XOR survives
  only as *gate extraction* inside congruence closure, never as Gauss.
- **Cardinality / at-most-k detection** — absent.
- **Local-search minimum caching and reuse** — absent.
- **Blocked clause elimination** — **[re-verified]** absent as a simplifier.
  `grep -rl blocked references/kissat/src` matches exactly one file, `src/check.c`,
  where `checker_blocked_literal` is the RAT test inside the debug proof checker.
  **Kissat, the strongest single-core sequential SAT solver, ships no BCE.**
- **Parallel clause import/export** — `src/kissat.h` exposes no sharing API.
  `src/import.c` is external↔internal *variable* mapping only.

### NEWS says removed, source says present

These are live disagreements. In every case the source wins.

| Technique | `NEWS.md` (sc2022-light) | 4.0.4 source |
| --- | --- | --- |
| Transitive reduction | removed | on by default (`src/transitive.c:299`) |
| Trail reuse on restart | removed/disabled | on by default (`src/restart.c:86`) |
| Vivification of irredundant clauses | removed | on by default (`src/vivify.c:1384`); NEWS 3.1.0 confirms re-addition |
| Eager subsumption of learned clauses | removed | on by default (`src/learn.c:145`) |
| XOR gate extraction | removed from BVE | present, but **relocated** into congruence closure (`congruencexors=1`), not `src/gates.c` |
| Failed-literal probing | removed | *partially* back: `src/backbone.c:572` is FLP restricted to literals in binary clauses. No general FLP. |
| Keeping untried candidates | removed (options deleted) | back: `transitivekeep=1`; vivify and backbone keep candidates unconditionally |
| BVE priority queue | removed in sc2022-bulky | back: `src/eliminate.c:131` uses a score min-heap |

The general lesson matches the Bitwuzla half: **a solver's own release notes are
a changelog of intent, not an inventory of the tree.** Six techniques listed as
removed are shipping and on by default.

## 2.5 Kissat scheduling, in prose

Search runs `src/search.c:194-223` as a strict `else if` chain, so an earlier
phase starves the later ones within one iteration.

Each simplifier owns a conflict limit updated on exit by `UPDATE_CONFLICT_LIMIT`
(`src/kimits.h:112`): the base interval option is multiplied by a growth function
of how many times it has already run — `SQRT` for reduce, `LINEAR` for reorder,
`LOGN` for random-decision bursts, `NLOGN` for probe, `NLOG2N` for eliminate,
`NLOG3N` for rephase. Probe and eliminate are additionally scaled U-shaped by
formula size (`src/kimits.c:39`), so both very small and very large formulas get
simplified more often than mid-sized ones.

Within a probing call (`src/probe.c:26`) the order is fixed: congruence →
substitute → backbone → vivify → sweep → substitute → transitive → backbone →
factor, repeated up to `proberounds=2`, stopping early if no variable count
changed. Preprocessing (`src/probe.c:45`) runs a different, shorter order —
congruence → backbone → sweep → substitute → factor — each behind its own
`preprocess*` flag, with `fastel` after it (`src/preprocess.c:73`).

Inside a call, work is bounded by **ticks, not conflicts**: `SET_EFFORT_LIMIT`
(`src/kimits.h:135`) grants `effort_per_mille × (search ticks since this
simplifier last ran)`, floored at `mineffort=10` million. Ticks count cache lines
touched during propagation (`src/proplit.h:66`), which makes budgets roughly
machine-independent. Vivification then subdivides its one budget across four
tiers in the ratio 3:3:1:3.

Mode switching (`src/mode.c:186`) alternates its own trigger: odd switches fire
on ticks spent in the previous mode, even switches on conflicts, starting from
`modeinit=1e3`. Rephasing runs only in stable mode; reordering runs in both.

---

# 3. CaDiCaL 3.0.1

`references/cadical/VERSION` reads `3.0.1`; HEAD is `c607304`, 2026-07-19,
"updated year". Depth-1 clone, so `git log` cannot establish removals; every
"removed" claim below comes from `NEWS.md` or from absence in the tree.

`options.hpp` field order is `NAME, DEFAULT, LO, HI, O, P, R, USAGE`
(confirmed against `struct Option` at `src/options.hpp:317`). Every Default cell
is that DEFAULT field verbatim. Claims marked **[re-verified]** were checked a
second time by this lane against `src/options.hpp` and the call sites.

## 3.1 Search core

| Name | File:line | Default | What it does | Prov |
| --- | --- | --- | --- | --- |
| CDCL loop with interleaved inprocessing | `src/internal.cpp:280` | n/a | Fixed priority: propagate/analyze → unit iteration → external propagation → model check → limits → restart → rephase → reduce → inprobe → elim → compact → condition → decide. | `[C]` |
| Two-watched-literal propagation | `src/propagate.cpp:221` | n/a | Blocking literals; binaries handled inline without dereferencing the clause. | `[C]` |
| Blocking literal in the watch struct | `src/watch.hpp:31` | n/a | 16-byte `Watch{Clause*, blit, size}`; `binary()` is `size==2`, so there is **no separate binary watch list**. | `[C]` |
| **Intel-SAT watch invariant** | `src/watch.hpp:20` | n/a | Maintains: if a watched literal is false, either it will be propagated or its blocking literal is true at a lower level (LIPIcs.SAT.2022.8). | `[C]` |
| **Clause search position (`pos`)** | `src/clause.hpp:98` | n/a | Gent 2013 "position of last watch replacement" — the search for a new watch resumes where it stopped rather than at the start. | `[C]` |
| `propergate` (re-propagate for flipping) | `src/propagate.cpp:497` | n/a | Blocking-literal-free re-propagation so that `flip()` on a model is sound. | `[C]` |
| Stable/focused mode switching | `src/restart.cpp:18` | on (`stabilize`=1) | Interval measured in **ticks**, growing as `inc.stabilize × stabphases²`. | `[C]` |
| Stable-only mode | `src/restart.cpp:22` | off (`stabilizeonly`=0) | | `[C]` |
| **Per-mode compiled specializations** | `src/stable.cpp:7`, `src/unstable.cpp:6` | n/a | Separate compiled instantiations of propagate/analyze/decide per mode — the mode test is hoisted out of the hot loop entirely. | `[C]` |
| EVSIDS scores (stable) | `src/analyze.cpp:105` | on (`score`=1) | `use_scores() = opts.score && stable` (`src/internal.hpp:476`); binary heap over `stab[]`. | `[C]` |
| VMTF queue (focused) | `src/decide.cpp:12` | n/a | Doubly-linked bump queue with a `queue.unassigned` pointer (SAT'15). | `[C]` |
| Score decay factor | `src/analyze.cpp:137` | `scorefactor`=950/1000 | EVSIDS increment growth per conflict. | `[C]` |
| Score rescaling | `src/analyze.cpp:85` | n/a | On overflow. | `[C]` |
| Variable bumping | `src/analyze.cpp:175` | on (`bump`=1) | Analyzed variables, sorted by enqueue stamp for VMTF. | `[C]` |
| Reason-side bumping | `src/analyze.cpp:359` | on (`bumpreason`=1) | To `bumpreasondepth`=1, `bumpreasonlimit`=10, gated by decision rate `bumpreasonrate`=100. | `[C]` |
| Clause bumping / glue recompute + promote | `src/analyze.cpp:206` | n/a | Recomputes glue of every resolved clause, promotes to a lower tier if it shrank, sets `used = max_used`. | `[C]` |
| Tier1/2/3 by glue | `src/clause.hpp:95` | `reducetier1glue`=2, `reducetier2glue`=6 | Chanseok Oh's three tiers; tier1 always kept, tier2 needs 2 unused intervals, tier3 one. | `[C]` |
| **Dynamic tier recomputation** | `src/tier.cpp:7` | on (`recomputetier`=1) | Recomputes the tier1/tier2 glue cutoffs from the *measured* bump histogram so tier1 covers `tier1limit`=50% and tier2 `tier2limit`=90% of bumps; rescheduled at `2^tierecomputed` conflicts, capped at 2^16. | `[C]` |
| Per-mode tier limits | `src/tier.cpp:26` | n/a | `tier1[stable]` / `tier2[stable]` are indexed by mode — stable and focused carry **different** cutoffs. | `[C]` |
| Clause reduction | `src/reduce.cpp:212` | on (`reduce`=1) | Sorts by (glue, size), collects `reducetarget`=75% of unused redundant clauses. | `[C]` |
| **Three-shape reduce interval** | `src/reduce.cpp:212` | `reduceint`=25, `reduceinit`=300, `reduceopt`=1 | `reduceopt` selects 0 = `prct` (quadratic in reduction count), 1 = `sqrt(conflicts)`, 2 = `log(conflicts)`; plus a `log10(irredundant/1e4)` stretch above 1e5 irredundant clauses. | `[C]` |
| Redundant flush | `src/reduce.cpp:34` | **off** (`flush`=0) | Periodically discards *all* unused redundant clauses; interval grows by `flushfactor`=3 from `flushint`=1e5. | `[C]` |
| Glucose EMA restarts | `src/restart.cpp:94` | on (`restart`=1) | `fast glue > margin × slow glue`; `restartmarginfocused`=10%, `restartmarginstable`=25%, base `restartint`=2. | `[C]` |
| Reluctant (Luby) doubling in stable | `src/reluctant.hpp:24` | on (`reluctant`=1) | Knuth's reluctant doubling *replaces* glue restarts while stable; `reluctantint`=1024, `reluctantmax`=1048576. | `[C]` |
| Trail reuse on restart | `src/restart.cpp:125` | on (`restartreusetrail`=1) | Heule's idea: backtrack only to the level whose decision still outranks the next decision. | `[C]` |
| Chronological backtracking | `src/analyze.cpp:656` | on (`chrono`=1) | SAT'18; triggers when `level − jump > chronolevelim`=100. | `[C]` |
| Forced-always chrono | `src/analyze.cpp:659` | off (`chronoalways`=0) | | `[C]` |
| Chrono trail reuse | `src/analyze.cpp:676` | on (`chronoreusetrail`=1) | Prefers chrono BT when it reuses trail (score/bump comparison against the next decision). | `[C]` |
| **Reassignment on backtrack** | `src/backtrack.cpp:120` | n/a | Out-of-order literals *survive* backtracking rather than being unassigned — the essence of the SAT'18 paper. | `[C]` |
| 1-UIP conflict analysis | `src/analyze.cpp:1021` | n/a | With conflict-level fixing for out-of-order trails. | `[C]` |
| On-the-fly self-subsumption (OTFS) | `src/analyze.cpp:932` | on (`otfs`=1) | Strengthens or subsumes the antecedent when the resolvent is a strict subset. | `[C]` |
| OTFS subsume | `src/analyze.cpp:900` | on (`otfs`=1) | A reason subsumed by the conflict is deleted rather than resolved. | `[C]` |
| OTFS backtrack level | `src/analyze.cpp:550` | on (`otfs`=1) | Recomputes the jump level after an OTFS strengthening. | `[C]` |
| **Recursive minimization with three abort rules** | `src/minimize.cpp:110` | on (`minimize`=1, `minimizedepth`=1e3) | Van Gelder "poison" marking, Knuth's single-seen-on-level abort, **plus a new early abort when the earliest seen literal was assigned later**. | `[C]` |
| Minimization tick accounting | `src/minimize.cpp:33` | on (`minimizeticks`=1) | Charges minimization to search ticks, which feeds every downstream effort budget. | `[C]` |
| All-UIP shrinking | `src/shrink.cpp:426` | on, full (`shrink`=3; 1 = binary-only, 2 = minimize-on-pulling) | Block-wise all-UIP shrinking of the 1-UIP clause. | `[C]` |
| **Reap: radix-bucketed monotone priority queue** | `src/reap.hpp:7` | on (`shrinkreap`=1) | A 33-bucket monotone queue used as the shrink frontier — a purpose-built data structure for one technique. | `[C]` |
| Eager subsumption of recent learned clauses | `src/analyze.cpp:729` | on (`eagersubsume`=1) | Against the last `eagersubsumelim`=20 learned clauses. | `[C]` |
| Phase saving | `src/decide.cpp:125` | n/a | `phases.saved` is the fallback in `decide_phase`. | `[C]` |
| Target phases | `src/backtrack.cpp:46` | on, **stable only** (`target`=1) | Phases of the largest conflict-free trail. | `[C]` |
| Best phases | `src/backtrack.cpp:66` | n/a | Largest-ever conflict-free trail; consumed by `rephase_best`. | `[C]` |
| Forced phase | `src/decide.cpp:126` | off (`forcephase`=0) | Always use `phase`=1. | `[C]` |
| **Rephasing schedule (8- or 12-cycle)** | `src/rephase.cpp:113` | on (`rephase`=1; 2 = stable-only), `rephaseint`=1e3 | Cycles inverted → best → flip → best → random → best → original → best (mod 8), or the same with walk interleaved (mod 12). Note the **`flip` kind, which Kissat does not have**. | `[C]` |
| Six rephase kinds | `src/rephase.cpp:39` (original), `:51` (inverted), `:63` (flip), `:74` (random), `:87` (best), `:100` (walk) | n/a | | `[C]` |
| "Stubborn I/O" focused phases | `src/decide.cpp:143` | **off** (`stubbornIOfocused`=0) | A Kissat port; requires `rephase`=2. Source comment calls it "does not seem very useful", and `decide.cpp:148` documents an eyeball change: "kissat has 3 but 5 looks better". | `[C]` |
| Random decisions | `src/decide.cpp:66` | **off** (`randec`=0) | Bursts of `randeclength × log(count)` conflicts; `randecfocused`=1, `randecstable`=0, `randecint`=500, `randecinit`=1e3 — so enabling `randec` alone gives focused-only bursts. | `[C]` |
| Reverse variable order | `src/decide.cpp:107` | off (`reverse`=0) | | `[P]` |
| Queue shuffling | `src/queue.cpp:60` | off (`shuffle`=0; `shufflequeue`=1) | `shufflerandom`=0 means reverse rather than random. | `[C]` |
| Score-heap shuffling | `src/score.cpp:18` | off (`shuffle`=0; `shufflescores`=1) | | `[C]` |
| Generic binary heap | `src/heap.hpp:24` | n/a | `heap<C>` reused for EVSIDS scores and for the elimination/blocking schedules. | `[C]` |
| **Radix sort** | `src/radix.hpp:39` | `radixsortlim`=32 | Generic stable `rsort`, introduced where `std::sort` was measured at up to 30% of runtime (bumping order). | `[C]` |
| Bias-corrected EMAs | `src/ema.hpp:14` | n/a | POS'15; windows `emagluefast`=33, `emaglueslow`=1e5, `ematrailfast`=1e2, `ematrailslow`=1e5, and `emasize`/`emajump`/`emalevel`/`emadecisions`=1e5. | `[C]` |
| **Per-mode EMA sets** | `src/averages.cpp:24` | n/a | Stable and focused each keep their own complete EMA set, swapped at every mode switch. A restart heuristic that does not carry statistics across the mode boundary. | `[C]` |
| Ticks as the universal budget | `src/limit.hpp:136` | n/a | `SET_EFFORT_LIMIT` derives each technique's budget from search ticks since its last run × `<name>effort`/1000, and **returns false** if the budget is below `<name>thresh × clauses.size()`. | `[C]` |
| Adaptive delay counters | `src/delay.hpp:8` | n/a | `bump_delay` doubles by increment, `reduce_delay` halves; used by sweep, congruence, and vivify-irredundant. | `[C]` |

## 3.2 Memory, arena, garbage collection

| Name | File:line | Default | What it does | Prov |
| --- | --- | --- | --- | --- |
| **Copying arena GC with locality-ordered layout** | `src/collect.cpp:525` | on (`arena`=1, from the first collection) | `arenatype`=3 selects the traversal order used to lay clauses out: 1 = clause order, 2 = variable order, **3 = decision-queue order** (the default). `arenasort`=1, `arenacompact`=1. The collector deliberately reorders the heap for cache locality along the expected decision path. | `[C]` |
| Clause-to-phase co-location | `src/decide.cpp:180` | n/a | `likely_phase` is consulted by the collector so that clauses likely accessed together land together. | `[C]` |
| Garbage binary removal | `src/collect.cpp:473` | n/a | A separate pass, because binaries live in watch lists. | `[C]` |
| Reason protection | `src/collect.cpp:103` | n/a | Reason clauses pinned across collection. | `[C]` |
| Compaction | `src/compact.cpp:162` | on (`compact`=1) | Renumbers away inactive variables at `compactint`=2e3 conflicts; needs `compactmin`=1e2 inactive and `compactlim`=1e2 per mille of `max_var`. | `[C]` |

## 3.3 Inprocessing

| Name | File:line | Default | What it does | Prov |
| --- | --- | --- | --- | --- |
| **Vivification** | `src/vivify.cpp:1729` | on (`vivify`=1) | ATE/ALE by propagation plus conflict analysis; `vivifyeffort`=50‰, delayed under `vivifythresh`=20. | `[C]` |
| Vivify tier scheduling | `src/vivify.cpp:1717` | tier1/2/3 all on | Four sequential rounds with proportional budgets: tier1 `vivifytier1eff`=4, tier2 = 2, tier3 = 1, irredundant `vivifyirredeff`=3. | `[C]` |
| **Vivify uses different tier boundaries from reduce** | `src/vivify.cpp:1717` | **off** (`vivifycalctier`=0) **[re-verified]** | By default vivification uses **hardcoded glue 2 and 6**, *not* the dynamically recomputed limits from `src/tier.cpp` that `reduce` uses. Enabling `vivifycalctier` switches it to `tier1[false]`/`tier2[false]`. Two subsystems disagree about what "tier1" means, by default. | `[C]` |
| Vivify-irredundant adaptive delay | `src/vivify.cpp:1875` | on (`vivifyirred`=1) | Bumps the delay if fewer than 1% of checks strengthen. | `[C]` |
| Vivify instantiation | `src/vivify.cpp:827` | on (`vivifyinst`=1) | Tries to instantiate the last literal of the candidate. | `[C]` |
| **Vivify can un-delete a clause** | `src/vivify.cpp:49` | n/a | Vivification can subsume, can **un-delete a garbage binary** that turns out to subsume, and can promote redundant → irredundant. | `[C]` |
| Vivify demote | `src/vivify.cpp` (near `:120`) | **off** (`vivifydemote`=0) | Turn an irredundant clause redundant instead of deleting it. Source comment: "turned out to not be useful, kept for the proof-tracer API". A technique retained solely because a proof format needs the event. | `[C]` |
| Vivify retry / once | `src/vivify.cpp:873` | `vivifyretry`=0, `vivifyonce`=0 | Re-vivify after success (0..5); vivify each clause only once (1 = redundant, 2 = both). | `[P]` |
| Vivify schedule cap | `src/vivify.cpp:1344` | `vivifyschedmax`=5e3 | Bounds the sort cost; unchecked clauses carry a `vivify` bit to the next round. | `[C]` |
| Vivify flush | `src/vivify.cpp:372` | on (`vivifyflush`=1) | Flush subsumed clauses out of the schedule between rounds. | `[C]` |
| **Bounded variable elimination** | `src/elim.cpp:1017` | on (`elim`=1) | SATeLite-style, as inprocessing; `elimint`=2e3 conflicts, `elimrounds`=2, `elimeffort`=1e3‰, `elimclslim`=1e2, `elimocclim`=1e2. | `[C]` |
| Elimination bound ratchet | `src/elim.cpp:963` | `elimboundmin`=0 → `elimboundmax`=16 | The bound is raised **only when a whole phase completed**. | `[C]` |
| Elimination candidate score | `src/elim.cpp:21` | `elimsum`=1, `elimprod`=1 | Ranks pivots by `prod·(pos·neg) + sum·(pos+neg)`. | `[C]` |
| Elimination by substitution | `src/elim.cpp:545` | on (`elimsubst`=1) | With a gate, resolve only gate × non-gate pairs. | `[C]` |
| — AND gates | `src/gates.cpp:319` | on (`elimands`=1) | | `[C]` |
| — Equivalence gates | `src/gates.cpp:200` | on (`elimequivs`=1) | | `[C]` |
| — ITE gates | `src/gates.cpp:501` | on (`elimites`=1) | From ternary clauses. | `[C]` |
| — XOR gates | `src/gates.cpp:632` | on (`elimxors`=1) | Up to `elimxorlim`=5. | `[C]` |
| **— Semantic definition mining with kitten** | `src/definition.cpp:178` | **off** (`elimdef`=0) **[re-verified]** | Runs the embedded `kitten` solver on the pivot's neighbourhood and reads a gate out of the UNSAT core; `elimdefcores`=1, `elimdefticks`=2e5. The strongest gate-extraction route in the tree, and it is disabled — whereas Kissat has the same idea on by default (`definitions=1`). | `[C]` |
| Eager backward subsumption in BVE | `src/backward.cpp:215` | on (`elimbackward`=1) | Backward-subsumes with each resolvent as it is added. | `[C]` |
| On-the-fly self-subsumption in BVE | `src/elim.cpp:209` | n/a | A resolvent that strictly subsumes an antecedent replaces it. | `[C]` |
| Resolution limiting | `src/elim.cpp:786` | on (`elimlimited`=1) | Caps resolutions per round between `elimmineff`=1e7 and `elimmaxeff`=2e9. | `[C]` |
| **Fast BVE** | `src/elimfast.cpp:449` | `fastelim`=1 **but unreachable at defaults** — see §3.4 **[re-verified]** | Cheap one-shot BVE, `fastelimbound`=8, `fastelimclslim`=1e2, `fastelimocclim`=100, `fastelimrounds`=4. | `[C]` |
| **Forward subsumption** | `src/subsume.cpp:335` | on (`subsume`=1) | Bayardo-inspired forward algorithm with one-watch occurrence connection; `subsumeeffort`=1e3‰, `subsumeclslim`=1e2, `subsumeocclim`=1e2, `subsumebinlim`=1e4. | `[C]` |
| Strengthening | `src/subsume.cpp:156` | on (`subsumestr`=1) | Self-subsuming resolution during the subsumption sweep. | `[C]` |
| Backward subsumption queue | `src/backward.cpp:40` | on (`elimbackward`=1) | Used **only** inside BVE. | `[C]` |
| **Failed-literal probing** | `src/probe.cpp:787` | on (`probe`=1) | Probes only *roots of the binary implication graph*; `probeeffort`=8‰, `probethresh`=0; leftover probes survive to the next call. | `[C]` |
| **Hyper binary resolution** | `src/probe.cpp:150` | on (`probehbr`=1) | Learns dominator-based binary clauses during probe propagation. **CaDiCaL has HBR on by default; Kissat removed it entirely.** | `[C]` |
| Failed-literal learning with LRAT chain | `src/probe.cpp:513` | n/a | Derives the unit and its proof chain when a probe conflicts. | `[C]` |
| Hyper unary resolution | `src/deduplicate.cpp:12` | on (`deduplicate`=1) | `(1 ∨ ¬2)` with `(1 ∨ 2)` gives the unit `1`; done in the dedup scan, not in probe. | `[C]` |
| Binary deduplication | `src/deduplicate.cpp:20` | on (`deduplicate`=1) | Watch-list scan. | `[C]` |
| Initial full deduplication | `src/deduplicate.cpp:208` | **off** (`deduplicateallinit`=0) | Removes duplicated clauses of *any* size once before the first solve. Added in 2.2.1 because 2.1.3 used to deduplicate all clauses inside vivification and stopped under stricter limits (issue #147) — an implicit behaviour turned into an opt-in option. | `[C]` |
| **Hyper ternary resolution** | `src/ternary.cpp:359` | on (`ternary`=1) | Ternary × ternary resolution (CPAIOR'13); **simulates structural hashing for MUX/XOR when combined with ELS**; `ternaryrounds`=2, `ternaryocclim`=1e2, `ternarymaxadd`=1e3%, `ternaryeffort`=8‰, `ternarythresh`=6. Kissat removed this; CaDiCaL runs it by default. | `[C]` |
| SCC decomposition + ELS | `src/decompose.cpp:736` | on (`decompose`=1) | Tarjan SCC over the BIG, equivalent-literal substitution; `decomposerounds`=2. | `[C]` |
| Transitive reduction of the BIG | `src/transred.cpp:11` | on (`transred`=1) | Removes transitive binary edges (bounding HBR blow-up) and finds some failed literals; `transredeffort`=1e2‰, max `transredmaxeff`=1e8. | `[C]` |
| **Blocked clause elimination** | `src/block.cpp:737` | **off** (`block`=0) **[re-verified]** | Move-to-front resolvent-tautology check; `blockminclslim`=2, `blockmaxclslim`=1e5, `blockocclim`=1e2. Called only from inside `elim`. | `[C]` |
| Pure literal elimination | `src/block.cpp:249` | off (with `block`) | A special case of BCE for literals with zero negative occurrences. **Note the consequence: with `block=0`, CaDiCaL has no standalone pure-literal rule.** | `[C]` |
| Single-negative-occurrence blocking | `src/block.cpp:298` | off (with `block`) | Cheap specialization when `¬lit` occurs once. | `[C]` |
| **Covered clause elimination (CCE/ACCE)** | `src/cover.cpp:645` | **off** (`cover`=0) **[re-verified]** | LPAR-10 / JAIR'15: asymmetric literal addition (ALA, by propagation) plus covered literal addition (CLA, by full occurrence lists); `covereffort`=4‰, `covermaxclslim`=1e5, `covermaxeff`=1e8. Called only from inside `elim`. | `[C]` |
| **Globally blocked clause elimination ("conditioning")** | `src/condition.cpp:895` | **off** (`condition`=0) **[re-verified]** | Kiesl's globally blocked clauses / conditional autarkies (ATVA'19). **The only technique in either solver that needs multi-literal witnesses on the extension stack**; `conditionint`=1e4, `conditioneffort`=100‰, `conditionmaxrat`=100, `conditionmaxeff`=1e7. | `[C]` |
| **Variable instantiation** | `src/instantiate.cpp:312` | **off** (`instantiate`=0) **[re-verified]** | Removes low-occurrence literals from long clauses by testing satisfaction; `instantiateclslim`=3, `instantiateocclim`=1, `instantiateonce`=1. Triggered at the end of an `elim_round` (`src/elim.cpp:923`). | `[C]` |
| **SAT sweeping (kitten)** | `src/sweep.cpp:1894` | on (`sweep`=1) | Bounded environment per variable, solved by the embedded kitten, yielding equivalences and units *semantically*; `sweepvars`=256, `sweepclauses`=1024, `sweepdepth`=2, `sweepmaxvars`=8192, `sweepmaxclauses`=3e5, `sweepmaxdepth`=3, `sweepeffort`=1e2‰, `sweepthresh`=5, `sweepfliprounds`=1. | `[C]` |
| Sweep backbone/partition refinement | `src/sweep.cpp:766` | on (with `sweep`) | Candidate backbone literals and equivalence partitions refined by kitten models and by literal flipping. | `[C]` |
| Sweep to completion | `src/sweep.cpp:1915` | off (`sweepcomplete`=0) | Removes the tick limit entirely. | `[C]` |
| Sweep randomization | `src/sweep.cpp:214` | off (`sweeprand`=0) | | `[P]` |
| **Congruence closure — the largest single technique** | `src/congruence.cpp:7779` | on (`congruence`=1) | Extracts AND/XOR/ITE gates from CNF, hashes them, merges gates with equal inputs. **7,925 lines** — larger than most whole SAT solvers. | `[C]` |
| — AND-gate extraction | `src/congruence.cpp:3415` | on (`congruenceand`=1), `congruenceandarity`=1e6 | | `[C]` |
| — XOR-gate extraction | `src/congruence.cpp:4355` | on (`congruencexor`=1), `congruencexorarity`=4, `congruencexorcounts`=1 | | `[C]` |
| — ITE-gate extraction | `src/congruence.cpp:7717` | on (`congruenceite`=1) | Via conditional-equivalence pairs (`extract_condeq_pairs`, `src/congruence.cpp:7507`). | `[C]` |
| — Binary extraction + ternary strengthening | `src/congruence.cpp:202` | on (`congruencebinaries`=1) | Subsumes the dedup pass when on. | `[C]` |
| — Unit / equivalence propagation with path compression | `src/congruence.cpp:4878` | on | | `[C]` |
| — Forward subsumption after merging | `src/congruence.cpp:4989` | on | | `[C]` |
| Binary-clause backbone | `src/backbone.cpp:601` | on (`backbone`=1) | Kissat-style, restricted to binary propagation; `backboneeffort`=20‰, `backbonerounds`=100 scaled by phase count, `backbonemaxrounds`=1e3, `backbonethresh`=5. | `[C]` |
| **Bounded variable addition (`factor`)** | `src/factor.cpp:935` | **off** (`factor`=0, changed from 1 in 3.0.1) **[re-verified]** | Reverse BVE: introduces extension variables by extended resolution over common clause structure; `factorsize`=5, `factoreffort`=50‰, `factoriniticks`=300M, `factordelay`=4, `factorcandrounds`=2, `factorthresh`=7. | `[C]` |
| — Self-subsuming quotients | `src/factor.cpp:569` | off (with `factor`) | Adds the shorter clause when a quotient self-subsumes. | `[C]` |
| — Fresh-variable score/phase seeding | `src/factor.cpp:776` | `factorunbump`=1 | New extension variables get the **lowest** importance ("as in kissat"). | `[C]` |
| — API contract check | `src/factor.cpp:921` | `factorcheck`=1 | Requires `declare_more_variables` when factor is on (2 = always check). | `[P]` |
| **Local search (ProbSAT walk)** | `src/walk.cpp:1048` | on (`walk`=1) | Break-value-scored random walk; `walkeffort`=80‰, `walkmaxeff`=1e7 (× 1e3 ticks), `walknonstable`=1, `walkredundant`=0. | `[C]` |
| Kissat-style full-occurrence walk | `src/walk_full_occs.cpp:926` | **off** (`walkfullocc`=0) | An alternative walk using full occurrence lists instead of single-watched. **926 lines of a second local-search implementation, off by default.** | `[C]` |
| **Warmup before walk** | `src/warmup.cpp:334` | on (`warmup`=1) | CDCL-propagates *through* conflicts, ignoring them, to seed the walk with a propagation-consistent assignment, updating target phases. | `[C]` |
| Outer local-search rounds | `src/internal.cpp:891` | n/a | Quadratically growing propagation limit per round; used as a pre-solve step and by `rephase_walk`. | `[C]` |
| **Lucky phases — seven probes** | `src/lucky.cpp:455` | on (`lucky`=1) | all-false, all-true, forward-false, backward-false, forward-true, backward-true, **positive-Horn, negative-Horn**. Kissat has six; CaDiCaL adds the two Horn probes. | `[C]` |
| Lucky with assumptions | `src/lucky.cpp:350` | on (`luckyassumptions`=1) | New in 2.2.0. | `[C]` |
| Lucky before and after preprocessing | `src/internal.cpp:806` | on (`luckyearly`=1, `luckylate`=1) | | `[C]` |

## 3.4 Incremental, proofs, API, tooling

| Name | File:line | Default | What it does | Prov |
| --- | --- | --- | --- | --- |
| Extension stack / witness reconstruction | `src/extend.cpp:121` | n/a | Sörensson/MiniSAT-style reconstruction (IJCAR'12): witness literals, clause ids, and **multi-literal witnesses** for conditioning. | `[C]` |
| Clause restore for incremental | `src/restore.cpp:84` | `restoreall`=0, `restoreflush`=0 | Recursively restores weakened clauses whose witness literal is re-introduced (SAT'19); `restoreall`=2 forces restoring everything. | `[C]` |
| Variable reactivation | `src/flags.cpp:89` | n/a | Brings eliminated/substituted variables back for incremental use. | `[C]` |
| **ILB (incremental lazy backtracking)** | `src/assume.cpp:550` | **off** (`ilb`=0; 1 = assumptions only, 2 = everything) | Keeps the trail across incremental calls. Note §1.9: **Bitwuzla forces `ilb=2` unconditionally**, so every Bitwuzla run uses a non-default CaDiCaL here. | `[C]` |
| **Clause elevation** | `src/external_propagate.cpp:955` | on, mode 2 (`elevate`, range −1..3) | Assigns a literal at a *lower* level when a newly added clause justifies it, instead of backtracking. `−1` disables and forces backtracking. This is the surviving remnant of the removed `reimply`; `src/analyze.cpp:965` still branches on `opts.elevate != 3`. | `[C]` |
| Incremental clause decay | `src/clause.cpp:625` | on (`incdecay`=1) | Decays clause usefulness when clauses are added incrementally; `incdecayint`=1e6. | `[C]` |
| Failed-assumption core extraction | `src/assume.cpp:77` | `checkfailed`=1 checks it | Minimal failing-assumption core by analysis over assumption reasons. | `[C]` |
| Constraint (clause assumption) | `src/constrain.cpp:5` | n/a | A single "constraint" clause behaving as a disjunctive assumption. | `[C]` |
| `implied` / entailed literals | `src/internal.cpp:424` | n/a | Literals entailed by assumptions after `propagate()` (renamed from `get_entrailed_literals` in 3.0.0). | `[C]` |
| Model flipping | `src/flip.cpp:5` | n/a | `flip`/`flippable` let a caller perturb a satisfying assignment; requires `propergate` first. | `[C]` |
| **Lookahead / cube generation** | `src/lookahead.cpp:286` | n/a | Root-probing lookahead returning the best decision literal; `Solver::lookahead()` at `src/cadical.hpp:539`. | `[C]` |
| Cube-and-conquer driver | `src/cadical.cpp:750` | n/a | The standalone app solves a `p inccnf` cube list one cube at a time. | `[C]` |
| **IPASIR-UP external propagator** | `src/external_propagate.cpp:363` | n/a | Full user-propagator interface: observed variables, lazy reasons, external clause import, decision override, forced backtrack, final model check. | `[C]` |
| External reason laziness | `src/external_propagate.cpp:734` | off (`exteagerreasons`=0) | Ask for reasons only when needed; `exteagerrecalc`=1 recomputes trail levels afterwards. | `[C]` |
| External clause watch selection | `src/external_propagate.cpp:546` | n/a | Picks the two best literals to watch in an imported clause (trail position vs level). | `[C]` |
| Forgettable external clauses | `src/external_propagate.cpp:1429` | n/a | Propagator-supplied clauses may be marked deletable. | `[C]` |
| Fixed-assignment listener | `src/cadical.hpp` (`FixedAssignmentListener`) | n/a | Callback when a variable becomes fixed (added 2.1.0). **This is the hook Bitwuzla's skeleton-preprocessing pass uses** (§1.3). | `[P]` |
| IPASIR C interface | `src/ipasir.cpp:6` | n/a | Over `ccadical`. | `[C]` |
| DRAT tracer | `src/drattracer.cpp:7` | off (`lrat`=0, `binary`=1) | Text or binary. | `[C]` |
| LRAT tracer | `src/lrattracer.cpp:9` | off (`lrat`=0) | With antecedents. | `[C]` |
| FRAT tracer | `src/frattracer.cpp:7` | off (`frat`=0) | 1 = frat(lrat), 2 = frat(drat). | `[C]` |
| VeriPB tracer | `src/veripbtracer.cpp:1` | off (`veripb`=0, range 0..4) | Pseudo-Boolean proofs; odd values check deletions, >2 uses drat. | `[C]` |
| IDRUP tracer | `src/idruptracer.cpp:7` | off (`idrup`=0) | Incremental DRUP. | `[C]` |
| LIDRUP tracer | `src/lidruptracer.cpp:1` | off (`lidrup`=0) | Linear incremental DRUP, **including UNKNOWN queries**. | `[C]` |
| **Pluggable `Tracer` observer API** | `src/tracer.hpp:18` | n/a | Virtual observer for every proof event: add original / add derived, delete, demote, weaken/restore, conclude, finalize. `contrib/CadiCraig` builds a Craig interpolator on it. Six proof formats are consumers of one event stream. | `[C]` |
| Internal DRAT checker | `src/checker.cpp:1` | off (`check`=0; `checkproof`=3 = both) | Forward RUP/RAT, inline. | `[C]` |
| Internal LRAT checker | `src/lratchecker.cpp:1` | off (`check`=0) | Checks antecedent chains inline. | `[C]` |
| Witness / assumption / constraint checking | `src/proof.cpp:158` | `checkwitness`=1, `checkassumptions`=1, `checkconstraint`=1 (all under `check`=0) | | `[C]` |
| Frozen-semantics checking | `src/restore.cpp:1` | off (`checkfrozen`=0) | Checks the freeze/melt contract. | `[P]` |
| **Solution-guided debugging** | `src/solution.cpp:13` | via `--sol <file>` | Sam Buss's trick: given a known solution, abort on the first learned clause that falsifies it. A debugging technique that localizes an unsoundness to the exact learned clause. | `[C]` |
| `kitten` embedded SAT solver | `src/kitten.c`, `src/kitten.h:14` | n/a | Small C CDCL with antecedent tracking and core extraction; the engine behind sweeping and `elimdef`. The same sub-solver idea as Kissat's. | `[C]` |
| Predefined configurations | `src/config.cpp:23` | `default` | `--sat` (elimeffort 10, stabilizeonly 1, subsumeeffort 60), `--unsat` (stabilize 0, walk 0), `--plain` (every option with P=1 off). | `[C]` |
| `-O[1-3]` option optimizer | `src/options.cpp` (`Options::optimize`) | n/a | Scales options whose O column is 1 (base 2) or 2 (base 10). A single knob that widens every effort limit together. | `[C]` |
| Environment-variable option override | `src/options.hpp:347` | n/a | `initialize_from_environment` lets any option be set from the environment. | `[C]` |
| **Mobical model-based tester** | `src/mobical.cpp:5663` | n/a | API-level fuzzer and delta-debugger over the whole external interface, **including propagator callbacks**. 5,663+ lines of test harness shipped in `src/`. | `[C]` |
| Profiling | `src/profile.cpp:55` | `profile`=2 (0..4) | Per-technique wall/process time. | `[C]` |
| Progress reporting | `src/report.cpp:167` | platform-dependent | One-character codes: `[`/`]` stable, `{`/`}` focused, `p` probe, `=` sweep, `c` congruence, `k` backbone, `-` reduce, `~` rephase. | `[C]` |
| Termination-check throttling | `src/internal.hpp` | `terminateint`=10 | Checks the terminator only every 10th opportunity. | `[C]` |

## 3.5 CaDiCaL — removed, default-off, and dead

### Four complete techniques reachable only through BVE

`block` (BCE), `cover` (CCE/ACCE), `condition` (globally blocked clauses), and
`instantiate` are each fully implemented and each **off by default**. All four
are called only from inside `elim` (`src/elim.cpp:1097-1101`, `src/elim.cpp:923`),
so a configuration that never runs BVE never runs any of them, even if the
options are turned on.

### Fast BVE is dead code at default settings **[re-verified]**

`fastelim` defaults to **1** and its four limit options are live, but
`elimfast()` has exactly one call site — `src/internal.cpp:788`, inside
`preprocess_quickly`. And `preprocess_quickly` (`src/internal.cpp:750`) opens
with:

```cpp
if (!opts.preprocesslight)
  return;
```

`preprocesslight` defaults to **0** (`src/options.hpp:163`), changed in 3.0.1.
The whole light-preprocessing pipeline behind that early return —
`extract_gates`+`decompose`, `binary_clauses_backbone`, `sweep`, `factor`, and
`elimfast` — never runs from this path. Congruence, backbone, sweep and factor
are still reachable through `inprobe`; **fast BVE is not reachable at all**.

This is the exact shape of the `elim_udiv` finding in Bitwuzla (§1.2), reached by
a different mechanism: there a call site was `&&`-ed with `false`, here an
enclosing function returns before it. In both cases the option that appears to
control the feature does nothing, and reading the option table alone would give
the wrong answer. **Read the call site, not the default.**

### Other default-off techniques

- `elimdef` — kitten-based semantic definition mining. Off. Kissat has the same
  technique on by default.
- `walkfullocc` — a second, Kissat-derived local search. Off.
- `flush` — periodic full flush of redundant clauses. Off.
- `ilb` — off (split from `ilbassumptions` in 2.2.0). Bitwuzla overrides to 2.
- `randec` — off, but `randecfocused`=1, so enabling it gives focused-only bursts.
- `shuffle`, `reverse` — off; determinism/diversification knobs.
- `deduplicateallinit` — off; an opt-in restoration of behaviour 2.1.3 had implicitly.
- `vivifycalctier` — off; see the tier-disagreement row in §3.3.
- `stubbornIOfocused` — off; a Kissat port the source itself calls not very useful.
- `sweepcomplete`, `sweeprand`, `vivifydemote`, `vivifyonce`, `vivifyretry`,
  `chronoalways`, `stabilizeonly`, `forcephase` — off; experimental variants retained.

### Removed from the tree

| Thing | Status | Note |
| --- | --- | --- |
| **`reimply`** | removed in 1.9.4 | `NEWS.md`: "Simplified code by removing reimply again (but keeping ILB)". Introduced in 1.7.3 to *elevate* out-of-order literals to their correct lower level and re-propagate. Its residue is the `elevate` option, which now only elevates on clause **addition**. |
| **`lratbuilder.cpp` / `.hpp`** | **absent from 3.0.1** | `src/lratchecker.cpp` (833 lines) is present; the builder is not. `NEWS.md` does not mention it and the depth-1 clone cannot bisect. **Did not verify where it went.** |
| `ilbassumptions` | merged into `ilb`=1 in 2.2.0 | |
| `get_entrailed_literals`, `reserve` | renamed to `implied`, `resize` in 3.0.0 | Breaking API changes. |
| `--safe` configuration | added 1.7.2, removed 1.7.3 | When `popen` was replaced by `pipe`/`fork`/`exec`/`waitpid`. |
| **`stabilizefactor`** | **the option does not exist** **[re-verified]** | `src/restart.cpp:12` still says stabilization grows geometrically "if `opts.stabilizefactor` is `200` percent". `grep -rn stabilizefactor references/cadical/src` matches that comment and nothing else. The actual code (`src/restart.cpp:59-62`) grows the interval as `inc.stabilize × stabphases²` in **ticks**, not conflicts. Source wins; the comment is stale. |

### `factor` was turned on and then off again in one release

`NEWS.md:5` records that bounded variable addition was **enabled by default in
3.0.0 and disabled again in 3.0.1**, explicitly to avoid forcing the
`declare_more_variables` API contract on users. The 2.2.0 notes had promised to
"activate factor by default with 3.0.0". A technique whose default flipped twice
inside two releases, for an API-compatibility reason rather than a performance
one.

## 3.6 CaDiCaL scheduling, in prose

Preprocessing (`src/internal.cpp:804`) runs `lucky_phases` → optional
`deduplicate_all_clauses` → `preprocess_quickly` (inert at defaults, §3.5) → up
to `lim.preprocessing` rounds of `preprocess_round`, each being `inprobe(false)`
→ `elim(false)` → `condition(false)`. A round "succeeds" only if it removed
variables or raised the elimination bound; otherwise the loop breaks. Local
search then runs before search proper.

In search (`src/internal.cpp:280`) the loop tests in strict priority:
propagate/analyze, unit iteration, external propagation, model check, limits,
restart, rephase, reduce, `inprobe`, `elim`, `compact`, `condition`, decide. So
restarts starve rephasing, rephasing starves reduction, and every inprocessing
technique is starved by all of them.

`inprobe` (`src/probe.cpp:914`) is the inprocessing bundle, with a fixed internal
order: dedup binaries → `decompose` → `ternary` (→ `decompose`) → `probe`
(→ `decompose`) → `extract_gates` (→ `decompose`) → `binary_clauses_backbone` →
dedup → `sweep` (→ `decompose`) → `vivify` → `transred` →
`binary_clauses_backbone` → `factor`. Cheap and reliable first, expensive and
speculative last; `decompose` is re-run after every step that can create new
binaries. It fires when `stats.conflicts >= lim.inprobe` **and** at least one
`reduce` has happened since the last phase, and the next limit is
`25 × inprobeint × log10(phases+9)` conflicts later — so the number of
inprocessing phases grows roughly as √conflicts.

Every technique inside then takes a **second, independent budget in ticks** via
`SET_EFFORT_LIMIT` (`src/limit.hpp:136`): budget = (search ticks since this
technique last ran) × `<name>effort`/1000, accumulated onto the technique's own
tick counter. If that budget falls below `<name>thresh × |clauses|`, the
technique refuses to run at all and returns immediately — which is how expensive
setup costs (vivify's schedule build, sweep's and factor's occurrence lists) get
amortized instead of paid every round. Sweep, congruence and vivify-irredundant
additionally carry `Delay` counters (`src/delay.hpp`) that double on an
unproductive round and halve on a productive one.

BVE has its own conflict interval (`elimint`=2e3) and its own inner loop:
alternate `elim_round` with `subsume_round`, then `block`, then `cover`, until
nothing changes or `elimrounds`=2 is hit. Only a **fully completed** phase raises
`lim.elimbound` toward `elimboundmax`=16.

Mode switching (`src/restart.cpp:18`) is measured in ticks per mode, with
`lim.stabilize` set from `inc.stabilize × stabphases²` against the *next* mode's
tick counter; the switch swaps the entire EMA set and flips `use_scores()` from
VMTF to EVSIDS.

## 3.7 CaDiCaL — what I did not verify

- Where `lratbuilder.cpp` went. Absent from 3.0.1; not mentioned in `NEWS.md`;
  unbisectable from a depth-1 clone.
- `vivifydemote`'s and `vivifyretry`'s exact line numbers (recorded as
  approximate / `[P]`).
- `terminateint`'s exact line in `src/internal.hpp`.
- The `contrib/CadiCraig` interpolator beyond the fact that it consumes the
  `Tracer` API.

---

# 4. Cross-cutting observations

These are stated as observations about the three sources, not as
recommendations, and not as a comparison to axeyum.

1. **The two SAT solvers disagree about which techniques are worth running, in
   both directions.** Kissat runs congruence closure, sweeping, BVA/factoring and
   general definition extraction by default and has deleted hyper binary and
   hyper ternary resolution outright. CaDiCaL runs hyper binary resolution
   (`probehbr`=1) and hyper ternary resolution (`ternary`=1) by default and
   disables factoring and kitten-based definition mining. Same author, same year,
   opposite defaults on four techniques.

2. **Blocked clause elimination is off in one and absent from the other.** The
   brief noted that BCE measured negative in one controlled study and strictly
   better than Plaisted-Greenbaum in another. Both defaults are consistent with
   both results being true on different populations: CaDiCaL keeps a complete
   BCE implementation but ships it off (`block`=0), and Kissat carries no BCE
   simplifier at all — only the RAT test inside its debug proof checker.
   Recorded, not resolved.

3. **Three of the three subjects have a technique that the option table says is
   enabled but that no execution path reaches.** Bitwuzla's `elim_udiv`
   (`if (false && …)`), CaDiCaL's `elimfast` (behind `preprocesslight`=0), and
   Kissat's `walkinitially` (read by no source file). The mechanisms differ; the
   observable is identical, and in all three cases the option's default is a lie
   about behaviour. This lane's method — read the call site, not the option
   table — was necessary in every case.

4. **Both SAT solvers embed a second, smaller SAT solver.** `kitten` appears in
   both trees and serves the same two jobs: semantic gate/definition extraction
   from an UNSAT core, and SAT sweeping. In Kissat both uses are on by default; in
   CaDiCaL only sweeping is. The reusable pattern is "an UNSAT core from a bounded
   sub-problem *is* the structural fact you wanted", replacing syntactic pattern
   matching.

5. **Effort is denominated in ticks (cache lines touched), not conflicts or
   time**, in both SAT solvers, with an explicit refusal-to-run threshold below
   which a technique returns rather than doing partial work. Both then layer
   adaptive delay counters on top for the techniques whose yield is lumpy.
   Bitwuzla's analogue is different in kind: it denominates in *AIG AND gates*
   and uses the estimate to accept or reject a transformation rather than to
   budget one.

6. **Three separate places use a cost model to decide whether a sound
   transformation is worth applying**, rather than applying it unconditionally:
   Bitwuzla's `AigScore` referee over normalization (§1.4), Bitwuzla's offline
   `AbstractionLemmaScorer` that ranks and *verifies* lemma schemas before
   freezing the ranking into source (§1.6), and CaDiCaL/Kissat's tick thresholds.
   The Bitwuzla lemma scorer is the only one of the three that also **proves** its
   candidates before shipping them.

7. **Release notes are a changelog of intent, not an inventory.** Six techniques
   Kissat's `NEWS.md` lists as removed are shipping and on by default; Bitwuzla's
   CAV 2023 pass list names a pass that has been deleted; CaDiCaL's `restart.cpp`
   comment describes an option that does not exist. In every case the source won.

