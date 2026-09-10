# Word-level rewrite depth: is the 296-vs-59 rule gap costing us AIG?

Roadmap item 3.3 of
[`docs/solver-comparison-2026-09/11-roadmap-and-plan.md`](../../solver-comparison-2026-09/11-roadmap-and-plan.md),
measured 2026-09-10 on `474423c8d`. Lane M3-3.

**Recommendation: DO NOT BUILD.** Not "defer" — the rule-count framing is the
wrong measurement, and closing the gap as stated would make the instances we
actually lose *worse*, not better. There is a four-item carve-out at the end, and
its highest-value item is an encoding option we already have and leave off, not a
rewrite rule.

## The question, as a number

Three questions, each with an answer:

1. **How many AND gates does each missing rule remove from the circuit our
   lowering actually builds?** For 14 of 25 candidate rules the answer is
   **zero**, measured. For two it is **negative** — the rewrite makes our
   circuit bigger.
2. **How many opportunities for the missing rules exist in input we see?** On
   352,479 post-rewrite term nodes across 123 real SMT-LIB QF_BV instances, the
   four most frequent missing-rule classes account for 43,582 firings — 79% of
   the top five — and all four have a measured per-firing delta of **zero**. The
   two classes with a real per-firing win fire on 0.34% of nodes each.
3. **Are the 43 satisfiable instances we miss (item 3.1's side finding) large
   because of missing rewrites?** No. **17 of the 43 cannot finish the word-level
   rewriting we already run** in 300 s with a 20 GB address-space cap, and 12 of
   those 17 are exactly the files the front door reports as
   `preprocessing timeout before reduced dispatch`. On the 26 that do finish,
   rewriting *grows* the AIG.

## First, the two rule counts are not comparable

`296` and `59` count different things, and `10-gap-analysis.md` row 10 sets them
side by side without saying so.

Bitwuzla's `RewriteRuleKind`
(`references/bitwuzla/src/rewrite/rewriter.h:372-829`, clone
`a5e6e8a7ad511975c495455924d0868bcdc304ea`) does have 296 entries. Note the path:
the comparison document cites `src/lib/rewrite/rewriter.h`, which does not exist
in the current clone.

```
$ awk '/enum class RewriteRuleKind/,/^};/' \
    references/bitwuzla/src/rewrite/rewriter.h | grep -cE '^\s+[A-Z][A-Z0-9_]*,\s*$'
296
```

Split by the file's own section comments and the rule-name suffix:

| bucket | count | why it is not a gap for us |
|---|---:|---|
| FP rewrites | 44 | We eliminate floating point at parse (ADR-0028). A rewrite over an FP term never sees one. |
| `*_ELIM` | 42 | Operator elimination: `BV_NAND_ELIM`, `BV_SDIV_ELIM`, `BV_SGE_ELIM`, `BV_ROL_ELIM`, `BV_ZERO_EXTEND_ELIM`, the overflow predicates, … Bitwuzla needs these because its bit-blaster has a **smaller base operator set**. Ours lowers `BvNand`, `BvNor`, `BvXnor`, `BvSdiv`, `BvSrem`, `BvSmod`, `BvComp`, all eight comparisons, both extends, both rotates and `repeat` natively (`crates/axeyum-bv/src/lib.rs`). Applying them to us is a no-op at best. |
| `*_EVAL` | 58 | Constant folding, one rule per operator. Our two folds (`bv.const_fold.v1`, `bool.const_fold.v1`) are gated on the **operands** rather than the operator, so one entry of ours covers the family. Measured residue: 0 of 14,963,085 post-rewrite nodes on the missed set, 61 of 352,479 on the decided set. |
| `NORM_*` | 13 | Normalization/factoring. One of these, `NORM_BV_ADD_MUL`, is on the carve-out list. |
| everything else | 139 | The real comparison surface. Our 59 (`crates/axeyum-rewrite/src/canonical.rs:47-105`) overlap it heavily. |

Total non-FP: 252. "We are missing 237 rules" is not a statement anyone measured;
the comparable surface is 139 plus 13, and 59 of ours sit inside it.

## Measurement 1 — the roadmap's own gate, per rule

The roadmap's exit criterion is *"measure AIG size before/after on the parity
slice per candidate rule"*. Applied to a minimal instance of each candidate: build
the rule's left-hand side and right-hand side as two terms, lower both with the
shipping eager `lower_terms`, count **AND gates**.

Counting method matters. `Aig::node_count` also counts the constant node and one
node per primary input, so a raw node-count comparison credits a rule with the 32
inputs it happens to drop and reports a 32-node "saving" where no gate moved. The
first pass of this measurement did exactly that. These are AND gates only.

The probe is kept, `#[ignore]`d, as
`crates/axeyum-bv/tests/rewrite_rule_aig_neutrality.rs`:

```
$ cargo test -p axeyum-bv --release --test rewrite_rule_aig_neutrality -- --ignored --nocapture
running 3 tests
BV_SHL_CONST	lhs=0	rhs=0	delta=0
BV_SHR_CONST	lhs=0	rhs=0	delta=0
BV_ASHR_CONST	lhs=0	rhs=0	delta=0
BV_MUL_POW2	lhs=0	rhs=0	delta=0
BV_UDIV_POW2	lhs=0	rhs=0	delta=0
BV_ULT_SPECIAL_CONST	lhs=0	rhs=0	delta=0
BV_ADD_SAME	lhs=0	rhs=0	delta=0
BV_ADD_NOT	lhs=0	rhs=0	delta=0
BV_SUB_SAME	lhs=0	rhs=0	delta=0
BV_CONCAT_CONST	lhs=0	rhs=0	delta=0
BV_EXTRACT_CONCAT	lhs=0	rhs=0	delta=0
BV_MUL_CONST_SHL	lhs=467	rhs=467	delta=0
BV_AND_CONCAT	lhs=32	rhs=32	delta=0
EQUAL_CONST_BV_NOT	lhs=31	rhs=31	delta=0
test rules_that_cost_zero_aig_gates ... ok
BV_MUL_ITE	lhs=4933	rhs=9770	delta=-4837
ITE_BV_OP	lhs=128	rhs=160	delta=-32
test rules_that_would_grow_the_aig ... ok
BV_UDIV_SAME	lhs=17234	rhs=31	delta=17203
NORM_BV_ADD_MUL	lhs=9957	rhs=5120	delta=4837
BV_EXTRACT_ADD_MUL	lhs=4837	rhs=253	delta=4584
EQUAL_BV_ADD	lhs=693	rhs=127	delta=566
ITE_THEN_ITE1	lhs=192	rhs=96	delta=96
test rules_that_remove_aig_gates ... ok

test result: ok. 3 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out
```

**Why the zeros happen, mechanically.** `Aig::and`
(`crates/axeyum-aig/src/lib.rs:345`, `simplify_and` at `:801`) folds constant
literals and hash-conses on the way in. So:

- `lower_shift_op` (`crates/axeyum-bv/src/lib.rs:2560`) builds a full logarithmic
  barrel shifter **unconditionally**, but a constant shift amount makes every
  stage's mux selector a constant literal and the whole shifter folds to wiring —
  0 gates. `BV_SHL_CONST`, `BV_SHR_CONST` and `BV_ASHR_CONST` have nothing left
  to remove. The in-range guard folds too: both its comparator operands are
  constant.
- `lower_mul_op` (`:2278`) is shift-and-add with each partial product gated by a
  multiplier bit. A constant multiplier makes that gate constant, so the zero
  bits' partial products vanish and the survivors are exactly the decomposition
  `BV_MUL_CONST_SHL`/`BV_MUL_CONST_ADD` would have produced. Both sides: **467
  gates** for `x * 100` at width 32.
- `x + x` and `x + ~x` collapse in the ripple adder for the same reason.

`BV_MUL_POW2`, `BV_UDIV_POW2`, `BV_SUB_SAME` and `BV_EXTRACT_CONCAT` are rules we
**do** ship and are in the zero list on purpose: they are the control showing the
zeros are a property of the lowering, not of a comparison that never ran.

**Two Bitwuzla rules would hurt us.** `BV_MUL_ITE` and `ITE_BV_OP` push an
operator into an `ite`'s branches, duplicating it: +4,837 and +32 gates on our
path. That is not a Bitwuzla error — a solver that reasons over terms gets value
a bit-blaster does not — but it is a direct counterexample to "land Bitwuzla's
rules".

## Measurement 2 — do the missing rules fire on input we see?

A rule that removes gates is worth nothing if nothing triggers it. A throwaway
`axeyum-bench` example walked each benchmark's term DAG **after** the shipping
one-round word-level pipeline and counted structural matches for 26 opportunity
classes, each named for the Bitwuzla rules it stands for. (25 on the committed
and missed sets: the `EXTRACT_OVER_STRUCT`/`EXTRACT_OVER_ARITH` split was added
afterwards and only re-run on the 123-instance set, so those two corpora report
the combined `EXTRACT_OVER_OP`.) Counting *after* the rewriting is the point: a
pre-rewrite count measures our own rules' input, not the residue Bitwuzla's rules
would see.

| corpus | files | post-rewrite term nodes | AND gates after rewriting |
|---|---:|---:|---:|
| committed `QF_BV` (`corpus/**`, `set-logic QF_BV`) | 107 (97 parsed) | 2,884 | 266,168 |
| SMT-LIB 2024 QF_BV `:status sat`, front door decides | 123 | 352,479 | 27,241,946 |
| SMT-LIB 2024 QF_BV `:status sat`, front door misses | 43 (26 finished) | 14,963,085 | 355,153,594 |

The last two are item 3.1's 166-instance size-stratified sample (five bands, seed
20260910) of the 46,191-file NAS set at
`/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/QF_BV`
(mounted; NFS from `nas3:/volume1/data`).

**Ten of the 107 committed QF_BV files do not parse.** They are
`corpus/regression/cvc5/qf_bv/cvc5__cli__regress0__bv__holes__ite-*.smt2`, they
use `bvite`, and they are cvc5's own ITE-rewrite regressions — the exact files
that would exercise the rule family this item is largely about.

### The distribution, on the 123 decided SMT-LIB instances

Firing counts over 352,479 post-rewrite term nodes, with the measured per-firing
AND-gate delta from measurement 1 beside each:

| opportunity class (Bitwuzla rules) | firings | files | gates removed per firing |
|---|---:|---:|---|
| `SHIFT_CONST` (`BV_SHL/SHR/ASHR_CONST`) | 24,845 | 95 | **0** |
| `ADD_CONST` (`BV_ADD_CONST`, `_SPECIAL_CONST`) | 11,386 | 82 | **0** (we ship the fold; `(x+3)+5` measured 248 → 112) |
| `MUL_CONST` (`BV_MUL_CONST`, `_CONST_SHL`, `_CONST_ADD`) | 3,865 | 42 | **0** |
| `SAME_ARGS_CHEAP` (`BV_ADD_SAME`, `BV_XOR_SAME`, …) | 3,486 | 19 | **0** |
| `EQ_ITE_RULE` (`EQUAL_ITE*`) | 2,292 | 4 | not measured individually |
| `AND_CONST` (`AND_CONST`, `BV_AND_SPECIAL_CONST`, …) | 1,828 | 57 | **0** |
| `CONCAT_STRUCT` (`BV_CONCAT_CONST`, `_EXTRACT`, `_AND`) | 1,298 | 8 | **0** on both cases measured |
| `EXTRACT_OVER_STRUCT` (`BV_EXTRACT_CONCAT*`, `_AND`, `_ITE`) | 1,279 | 23 | **0** (we ship most of these) |
| `NORM_ADD_MUL` (`NORM_BV_ADD_MUL` and kin) | 1,197 | 16 | **4,837** at w32, **19,909** at w64 |
| `EXTRACT_OVER_ARITH` (`BV_EXTRACT_ADD_MUL`) | 1,193 | 25 | **4,584** for a mul, 216 for an add |
| `AND_XOR` (`BV_AND_XOR`, `_XNOR`, `_CONCAT`) | 756 | 6 | 0 on the case measured |
| `CMP_SPECIAL_CONST` (`BV_ULT/SLT_SPECIAL_CONST`) | 508 | 58 | **0** |
| `EVAL_RESIDUE` (all 58 `*_EVAL`) | 61 | 9 | **0** — they *are* constant folds |
| `EQ_CONST_OP` (`EQUAL_CONST_BV_ADD/MUL/NOT`) | 61 | 13 | 0 on the case measured |
| `ITE_CONST_BRANCH` (`BV_*_ITE`, `ITE_BV_OP`) | 34 | 2 | **negative** on both cases measured |
| `AND_TWO_LEVEL` (`AND_IDEM/CONTRA/SUBSUM/RESOL`, 22 rules) | 6 | 2 | 32 |
| `EQ_SHARED_ARG` (`EQUAL_BV_ADD/SUB/CONCAT`) | 1 | 1 | 566 |
| `ITE_SAME_COND` (`ITE_THEN_ITE1-3`, `ITE_ELSE_ITE1-3`) | **0** | 0 | 96 |
| `SAME_ARGS_DIVREM` (`BV_UDIV_SAME`, `BV_UREM_SAME`) | **0** | 0 | 17,203 |
| `MUL_POW2_RESIDUE`, `SHIFT_SPECIAL`, `NOT_ARG`, `NEG_ARG`, `WIDTH1_OP` | 0 | 0 | — |

**This is the finding.** The distribution is neither long-tailed nor headed by
ten good rules. It is headed by rules whose measured AIG delta is **zero**: the
top four classes are 43,582 firings of the 45,874 in the top five, and all four
are already free. The two classes with a real per-firing win, `NORM_ADD_MUL` and
`EXTRACT_OVER_ARITH`, together fire 2,390 times — 0.68% of nodes. The rule with
the *largest* per-firing win, `BV_UDIV_SAME` at 17,203 gates, never fires at all.

The same shape holds on the other two corpora. Committed QF_BV (2,884 nodes):
`EXTRACT_OVER_OP` 212, `ADD_CONST` 146, `CONCAT_STRUCT` 75, `SHIFT_CONST` 48,
`EVAL_RESIDUE` 45, `AND_CONST` 36, `NORM_ADD_MUL` 1, `ITE_SAME_COND` 0,
`AND_TWO_LEVEL` 0, `SAME_ARGS_DIVREM` 0. The missed set (14,963,085 nodes):
`ADD_CONST` 29,304, `SHIFT_CONST` 9,931, `AND_CONST` 9,915, `NORM_ADD_MUL` 732,
`EQ_ITE_RULE` 262, `ITE_SAME_COND` 0, `EVAL_RESIDUE` 0.

### Two matchers were wrong, and the correction is the reason to distrust raw counts

The first pass counted "an `ite` under an `ite`" as an `ITE_THEN_ITE*`
opportunity and "an equality with an `ite` operand" as an `EQUAL_ITE*` one. Both
are just decision trees; no Bitwuzla rule fires on either. Requiring what the
rules require — the inner condition must be the outer one or its negation — moved
the counts by two orders of magnitude:

| corpus | `ITE_NESTED_ANY` (loose) | `ITE_SAME_COND` (what the rules need) | `EQ_ITE_ANY` (loose) | `EQ_ITE_RULE` |
|---|---:|---:|---:|---:|
| committed | 347 | **0** | 185 | 1 |
| decided (123) | 10,492 | **0** | 31,451 | 2,292 |
| missed (26) | 4,649,890 | **0** | 31,502 | 262 |

Both are reported so the gap is visible rather than tidied away. On the missed
set the loose class is 31% of all term nodes and the strict one is zero — if this
note had shipped the first pass, its headline would have been the opposite of the
truth.

### Controls

A hand-built fixture plants one instance of each class that reports zero on the
corpora. Every one fires, so the zeros above are real negatives and not a dead
matcher:

```
$ M33_NOLOWER=1 m33_rewrite_gap_probe <fixture with 21 term nodes>
ITE_SAME_COND       pre=2  post=2
SAME_ARGS_DIVREM    pre=2  post=2
NORM_ADD_MUL        pre=1  post=1
EXTRACT_OVER_ARITH  pre=1  post=1
EQ_ITE_RULE         pre=1  post=1
AND_TWO_LEVEL       pre=1  post=0     <- our canonicalizer removes it
WIDTH1_OP           pre=1  post=0     <- our canonicalizer removes it
```

The fixture is reproduced at the end of this note. Two further controls fire on
the real corpora: `MUL_POW2_RESIDUE` (a rule we ship) counts 3 and 170
pre-rewrite on the committed and decided sets and **0** post-rewrite on both;
`SHIFT_SPECIAL` goes 21 → 0 on the decided set; `EVAL_RESIDUE` goes 193 → 0 on
the missed set.

## Measurement 3 — the 43 satisfiable instances we miss

Item 3.1's side finding: the bit-blasting path fails 43 of 166 real satisfiable
SMT-LIB QF_BV instances at 10 s. If rewrite depth were why those formulas are too
big, that would be the strongest possible case for this item. It is not why.

### 3a. Seventeen of the 43 cannot finish the rewriting we already run

The probe was given **300 s and a 20 GB address-space cap per file** — 30x the
front door's budget. Seventeen files never got past the word-level rewriting:

```
17 files where the probe could not finish the word-level rewriting in 300 s / 20 GB:
  69,980,134  laby_22_22_11.lp.smt2
  69,979,587  laby_22_22_09.lp.smt2
  60,650,999  laby_21_21_18.lp.smt2
  60,650,980  laby_21_21_16.lp.smt2
  60,650,854  laby_21_21_12.lp.smt2
  44,566,191  laby_19_19_19.lp.smt2
  44,566,173  laby_19_19_14.lp.smt2
  44,566,076  laby_19_19_17.lp.smt2
  44,565,972  laby_19_19_16.lp.smt2
  37,720,016  laby_18_18_04.lp.smt2
  22,829,240  edge-matching-width=10-height=10-colours=15.smt2
  21,911,080  edge-matching-width=10-height=10-colours=13.smt2
  21,500,600  edge-matching-width=10-height=10-colours=12.smt2
  19,536,052  edge-matching-width=10-height=10-colours=5.smt2
  15,348,118  edge-matching-width=9-height=9-colours=15.smt2
  13,244,961  edge-matching-width=9-height=9-colours=8.smt2
   9,664,518  edge-matching-width=8-height=8-colours=14.smt2
```

Cross-checked against the front door's own verdicts from item 3.1's run, 12 of
these 17 are exactly the files it reports as
`unknown[preprocessing timeout before reduced dispatch]` — two independent runs
agreeing on which files the rewriting cannot process:

```
probe status x front-door verdict, on the 43 missed instances:
    1  probe=DIED_IN_rewrite       front door=HARDCAP
    3  probe=DIED_IN_rewrite       front door=unknown[preprocessed dispatch timeout after reduced solve]
   12  probe=DIED_IN_rewrite       front door=unknown[preprocessing timeout before reduced dispatch]
    1  probe=OK                    front door=HARDCAP
   10  probe=OK                    front door=unknown[combined-theory timeout after scalar backend]
    9  probe=OK                    front door=unknown[preprocessed dispatch timeout after reduced solve]
    3  probe=OK                    front door=unknown[preprocessing timeout before reduced dispatch]
```

**On 19 of the 43, the front door never reaches the solver at all.** Deeper
rewriting is a strictly negative change to those instances: it spends more of a
budget the current rewriting already exhausts.

### 3b. On the 26 that do finish, the rewriting makes the AIG bigger

| corpus | AND gates, unrewritten | AND gates, rewritten | per file: grew / shrank / unchanged |
|---|---:|---:|---|
| SMT-LIB decided (123) | 30,797,016 | 27,241,946 (−11.5%) | 40 / 46 / 37 |
| SMT-LIB missed (26 of 43) | 352,011,189 | 355,153,594 (**+0.9%**) | 13 / 6 / 7 |

This is not new. `reduction_shrinks_encoding`
(`crates/axeyum-solver/src/auto.rs:2344`) exists precisely because substitution
duplicates structure the term DAG was sharing, and its own docstring records
`062-bench_2195`, where the term DAG *shrank* while the AIG grew 46%. The front
door lowers both forms and keeps the smaller one, so this costs no verdicts
today — but it does mean term-level rewriting is not a size lever on these
instances, and "more rules" points the same way.

### 3c. They are big because they are big

| corpus | file size, median | AND gates, median | AND gates, p90 | AND gates, max |
|---|---:|---:|---:|---:|
| committed `QF_BV` (97) | 318 B | **0** | 1,831 | 127,089 |
| SMT-LIB decided sat (123) | 26,875 B | 54,082 | 577,020 | 1,997,785 |
| SMT-LIB missed sat (26) | 15,348,118 B | **2,158,128** | 46,072,867 | 113,989,742 |

The missed instances' median file size sits above the **95th percentile** of the
whole SMT-LIB 2024 QF_BV set (46,191 files: median 33,298 B, p95 3,328,641 B).
Their median circuit is 40x the decided set's, and the largest is 114 million AND
gates. A rule family that removes a few per cent of term nodes does not move an
instance across that gap.

The per-file table says the same thing:

```
 AIG AND gates   term DAG     size (B)  file
   113,989,742  1,998,122   90,036,157  SLL-NESTED-32-32-src-sp-not-excluded.smt2
   113,208,403  1,988,744   89,310,244  AND-NESTED-32-32-src-sp-not-excluded.smt2
    46,072,867  1,244,516   55,317,799  AND-NESTED-20-32-src-sp-not-excluded.smt2
    17,043,043    748,364   33,109,869  AND-NESTED-12-32-src-sp-not-excluded.smt2
    11,380,793  3,807,851   67,721,938  disjunctiveScheduling.in7.smt2
    11,122,979  4,063,516   72,378,291  disjunctiveScheduling.in8.smt2
     7,886,013    513,458   22,308,860  SLL-NESTED-8-32-src-sp-not-excluded.smt2
     6,528,625    188,396   11,645,651  gaussian.c.125.smt2
     5,391,633    721,420   11,992,756  sudoku.in7.smt2
     5,194,539    700,020   11,637,673  sudoku.in6.smt2
     5,185,329    699,020   11,621,084  sudoku.in3.smt2
     4,077,144      7,299      446,625  bench_15255.smt2
     2,158,128     15,911   12,832,194  bench_9501.smt2
     ...
       391,840          6          745  ndist.b.24491.smt2
```

The last row is the cleanest disproof available. `pspace/ndist.b.24491.smt2` is
**745 bytes** and its term DAG is **six nodes**:

```smt2
(declare-fun x () (_ BitVec 24491))
(declare-fun y () (_ BitVec 24491))
(assert (bvuge x y))
(assert (bvule (bvadd x (_ bv1 24491)) y))
```

391,840 AND gates, and the front door hits the node hardcap on it. No rewrite
rule among Bitwuzla's 296 fires on this term: it is a **bit-width** problem, and
it comes from Froehlich, Kovasznai and Biere's benchmark set built to demonstrate
exactly that bit-blasting scales in the width and not the syntax. The `laby_*`
and `edge-matching-*` families that dominate the rewrite timeouts are ASP
encodings whose size is in the instance, not in redundant term structure. The
`*-NESTED-*` files are Rosette output whose term histogram is `BoolAnd`
(2,061,309), `Ite` (1,793,751) and `Eq` (1,401,549) — and whose strict
`ITE_SAME_COND` count is zero.

## Recommendation

**DO NOT BUILD** a rule-count push toward 296, and do not add a level hierarchy
to gate rules whose measured value is zero at every level.

Four carve-outs, in value order. None of them is "add rewrite rules to reach 296":

1. **Turn on demand-sliced bit lowering, measured.** `BV_EXTRACT_ADD_MUL` is the
   largest firing-count × delta product in this note — 1,193 firings across 25 of
   123 instances at 4,584 gates for a multiplier — and it does not need a rewrite
   rule: `BitLoweringMode::DemandSliced` (`crates/axeyum-solver/src/backend.rs:79`)
   is the same idea implemented in the lowering, and the default is `Eager`
   (`:395`). This is a config-default question with a ready A/B, exactly the shape
   of item 1.2. **It belongs to the encoding lane, not to a rewriting lane.**
2. **`NORM_BV_ADD_MUL` (`x*y + x*z → x*(y+z)`), alone.** 4,837 gates at width 32
   and 19,909 at width 64, firing 1,197 times across 16 of the 123 decided
   instances. One rule, expressible in `canonical.rs`'s existing AC machinery,
   with a trivial `Preservation::Denotation` obligation. Gate it on a measured
   AIG reduction per instance, the way `reduction_shrinks_encoding` gates
   preprocessing — the distributive direction is not always the smaller one.
3. **A rewrite *budget*, not more rewrites.** 19 of 43 missed instances never
   reach the solver because preprocessing exhausts the budget. Item 1.5's
   `TickValve` is the machinery and is already built; its feed is the outstanding
   half. Making the rewriting *decline* on a 70 MB input is worth more than any
   rule in this note.
4. **`bvite` is a parse failure.** Ten committed QF_BV files — cvc5's own
   ITE-rewrite regressions — do not parse. They are the only committed files that
   would exercise the ITE rule family at all. Cheap, and unrelated to rewrite
   depth.

### What would change the answer

- **A corpus where the term structure is redundant *and* the circuit is small
  enough to solve.** Our committed QF_BV corpus cannot show this either way: its
  median instance lowers to **zero AND gates**, its largest file is 2,762 bytes,
  and its whole 97-file AIG is 266,168 gates — an eighth of one missed instance's
  median. Items 3.1 and 3.8 reached the same conclusion in their own domains. The
  set that would settle it is `20190311-bv-term-small-rw-Noetzli`, SMT-LIB's own
  *bit-vector term rewriting* family; we have vendored 4 of them into
  `corpus/qfbv-curated` and the NAS set has the rest.
- **A Bitwuzla head-to-head on AIG size.** Every delta here compares our lowering
  of a term against our lowering of its rewrite. The stronger measurement — our
  AIG against Bitwuzla's on the same instance — needs a Bitwuzla binary, which is
  not installed on this host. Nothing here rules out Bitwuzla's circuit being far
  smaller for another reason; it only rules out *these rules* as that reason.

## What I did not measure

- **Solve time.** Every number here is an AIG size or an opportunity count. No
  verdict changed and nothing was run through the solver; the verdicts quoted for
  the 166 SMT-LIB instances are item 3.1's, not re-measured.
- **Bitwuzla itself.** No binary on this host, so there is no measurement of
  Bitwuzla's own AIG for these instances, nor of its per-rule
  `HistogramStatistic`, which would give firing counts on its side rather than my
  structural approximation of them.
- **About 131 of the 252 non-FP rules.** The matchers name roughly 121 rules
  explicitly (the 58 `*_EVAL` as one class, plus about 63 others). Not matched,
  and therefore not counted anywhere above: the whole width-1 family
  (`BV_ADD_BV1`, `BV_MUL_BV1`, `BV_ULT_BV1`, `EQUAL_EQUAL_CONST_BV1`,
  `ITE_BOOL_TO_BV1`, `NOT_EQUAL_BV1_BOOL`, `BV_COMP_BV1_CONST`, …),
  `AND_BV_LT`/`AND_BV_LT_FALSE`, `EQUAL_INV`, `EQUAL_BV_MUL_UDIV_ZERO`,
  `ITE_COND_EQUAL`, `NOT_XOR`, `DISTINCT_CARD`, `BV_ADD_UREM`/`BV_ADD_SREM`,
  `BV_ADD_SHL`, `BV_ULT_CONCAT`/`BV_SLT_CONCAT`, 8 of the 13 `NORM_*`, and
  `ARRAY_PROP_SELECT`. `WIDTH1_OP` is a partial stand-in for the first of these
  and reports 0 on every corpus, which is a weak negative — width-1 bit-vectors
  are simply rare here.
- **Per-operator AIG cost attribution.** The probe has an exact mode for it
  (lower every subterm through one memoizing `IncrementalLowering` and attribute
  the delta) that was not run on the large files. Only operator *node* histograms
  are quoted above.
- **Whether the two classes with a real delta are worth their cost in wall
  clock.** `NORM_BV_ADD_MUL` needs a matcher over AC-flattened products; nothing
  here measures what that costs on a 4-million-node DAG, which is the number
  carve-out 2 has to clear.
- **Quantified, array, or `QF_ABV` input.** QF_BV only.
- **Whether the sample generalizes.** The 166 instances are item 3.1's
  size-stratified sample (five bands, seed 20260910), not a uniform draw, so the
  *absolute* size distribution over-represents the tail by construction. The
  conditional claim — within that sample, the instances we miss are far larger
  than the ones we decide — is what the numbers support.

## Reproducing

The per-rule AIG deltas are the `#[ignore]`d test committed with this note:

```sh
cargo test -p axeyum-bv --release --test rewrite_rule_aig_neutrality -- --ignored --nocapture
```

The corpus sweep used a throwaway `axeyum-bench` example
(`m33_rewrite_gap_probe`), deleted per the Phase 3 measurement brief. Per file it
did: parse; run the shipping one-round pipeline (`canonicalize_terms` →
`propagate_values` → `solve_eqs_bounded` → `elim_unconstrained` →
`canonicalize_terms`, mirroring `crates/axeyum-solver/src/preprocess.rs:160-251`
at `max_rounds = 1`, which is what `auto.rs:1932` calls); count reachable term
nodes and `lower_terms` AND gates before and after; and walk the term DAG
counting the 26 opportunity classes. It ran one file per process under
`timeout 300` and `ulimit -v 20000000` so an unfinishable file became a row
rather than killing the sweep, with the stage recorded on stderr — which is where
the `DIED_IN_rewrite` attribution comes from.

The control fixture:

```smt2
(set-logic QF_BV)
(set-info :status sat)
(declare-fun c () Bool)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun d () (_ BitVec 8))
(declare-fun e () (_ BitVec 8))
(declare-fun f () (_ BitVec 8))
(assert (= (ite c (ite c a b) d) e))              ; ITE_THEN_ITE1
(assert (= (ite c d (ite c a b)) f))              ; ITE_ELSE_ITE1
(assert (= (ite c a b) (ite c d e)))              ; EQUAL_ITE
(assert (= (bvudiv a a) (bvurem b b)))            ; BV_UDIV_SAME / BV_UREM_SAME
(assert (= (bvand (bvand a b) a) d))              ; AND_SUBSUM
(assert (= (bvadd (bvmul a b) (bvmul a d)) e))    ; NORM_BV_ADD_MUL
(assert (= ((_ extract 3 0) (bvmul a b)) ((_ extract 3 0) f)))  ; BV_EXTRACT_ADD_MUL
(declare-fun p () (_ BitVec 1))
(declare-fun q () (_ BitVec 1))
(assert (bvult p q))                              ; BV_ULT_BV1
(check-sat)
(exit)
```
