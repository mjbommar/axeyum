# NIA-ORDER-LEMMAS — what order and monotonicity lemmas are worth to OUR portfolio

Lane NIA-ORDER-LEMMAS, ADR-2136. ADR-2112 Part E named two lemma classes
present in z3 and **absent** from `nia_linearize.rs` — order lemmas
(`nla_order_lemmas.cpp`) and monotonicity lemmas (`nla_monotone_lemmas.cpp`) —
and its ablation measured what removing each is worth **to z3**, whose portfolio
is redundant enough that 66 of 75 files decide under every single-class removal.
That does not say what the two classes are worth to **us**. This lane measures
that.

Status: see §5 for the ship decision.

## 1. Sizing — the ceiling in files, per class (exit criterion 1)

`census_shared_factor.py` over all 116 undecided `QF_NIA` T1 rows
(`bench-results/nia-trace-20260915/undecided-116.txt`), **116 files, 0
errored**. Applicability is defined by the STEP each lemma takes, not by a name:

- **order** needs two DISTINCT nonlinear products sharing an operand term
  (`a·c` and `b·c`) — z3's `ac`/`bc`. A file with no such pair cannot emit one,
  whatever the model says.
- **monotonicity** needs a product at least one of whose factors carries no
  two-sided constant bound entailed by the top-level conjuncts. For a factor
  that IS two-sidedly bounded, `mccormick_lemmas` (`nia_linearize.rs:724`)
  already couples the magnitude and the monotonicity lemma adds nothing we
  have not got. This is exactly the population ADR-2112 §E1 claim 2 is about.

| | files of 116 |
|---|---:|
| **order lemma applicable** (≥ 1 shared-factor product pair) | **111** |
| **monotonicity applicable** (≥ 1 product with an unbounded factor) | **115** |
| both | 111 |
| neither | 1 (`ReachSafety-Loops/array_3-1-O0.smt2`, the word-only-fallback file ADR-2112 §A already excludes) |

Per-file shape, same 116 rows:

| column | min | median | p90 | max |
|---|---:|---:|---:|---:|
| nonlinear products | 0 | **242** | 1,911 | 38,472 |
| distinct product operands | 0 | 71 | 273 | 6,011 |
| operands shared by ≥ 2 products | 0 | **53** | 239 | 2,924 |
| shared-factor product PAIRS | 0 | **2,249** | 44,415 | **9,407,886** |
| most products on one operand | 0 | 14 | 52 | 574 |
| two-sidedly bounded terms | 0 | 26 | 107 | 16,529 |
| products with an unbounded factor | 0 | **242** | 1,911 | 38,472 |

Four files carry products but no shared factor at all
(`ps2-ll_unwindbound50-O0` 2 products, `MS_06` 36, `geo1-u_valuebound2-O0` 7,
`sqrtStep6a` 4).

**The two numbers that decide the design.** Applicability is nearly total
(111/116, 115/116), and the candidate set is enormous — the median file has
2,249 shared-factor pairs and one has 9.4 million. `unbounded_products` equals
`products` at every quantile: on this population **no product has both factors
two-sidedly bounded**, which is ADR-2112's "median 16 bounded symbols against
289 unbounded" restated per-product. So a static enumeration is out on both
counts, and a model-driven emission with a hard per-round cap is the only
shape that fits — which is also what z3 does (`order::order_lemma` runs off
`check_monomial` at the current assignment).

### 1.1 The census's controls

`--controls` runs 8 fixtures before any corpus file is read, and the census
REFUSES to run if one fails (exit 2):

| control | products | order | monotone |
|---|---:|---:|---:|
| `shared-factor-pair` (`a·c`, `b·c`) | 2 | 1 | 1 |
| `no-shared-factor` (`a·b`, `c·d`) | 2 | 0 | 1 |
| `linear-only-negative-control` | 0 | 0 | 0 |
| `lone-square-is-not-a-pair` (`a·a` alone) | 1 | **0** | 1 |
| `square-and-product-share-a-factor` (`a·a`, `a·b`) | 2 | **1** | 1 |
| `nary-left-assoc` (`(* a b c)` → two products) | 2 | 0 | 1 |
| `bounded-both-sides-no-monotone-need` | 1 | 0 | **0** |
| `let-bound-shared-factor` | 2 | 1 | 1 |

The last four are the discriminating ones: rows 4/5 separate "a lone square is
one monomial" from "the census never finds a shared factor", row 7 is the only
`monotone=0` with a product in it, and row 8 proves `let` is resolved rather
than treated as an opaque symbol.

`lone-square-is-not-a-pair` was written expecting `order=1` and the census said
`0`. The **expectation** was wrong, not the census: the order lemma couples two
DISTINCT monomials, and `a·a` against itself is vacuous. The expectation was
corrected and `square-and-product-share-a-factor` added beside it so the pair
still distinguishes.

### 1.2 The census against the engine's own count

The census is a text walk; the engine's count is computed on the normalized
polynomial. They are independent implementations of "how many nonlinear
products does this file have", so they are a control on each other. 89 of the
116 rows carry a `nonlinear abstraction: N cross-products` detail in
`bench-results/ledger/t1-QF_NIA-db31113fa.tsv` (`nra.rs:567`):

| | |
|---|---:|
| files where both counts are available | 89 |
| both nonzero | **89** |
| disagreements on nonzero-ness | **0** |
| census/engine ratio, min / median / max | 1.00 / **1.00** / 1.03 |

The first join of these two files matched **0 rows**, because the ledger's
`corpus_path` is corpus-relative and the undecided list is absolute. An empty
overlap would have read exactly like "the census disagrees with the engine
everywhere"; it was a join bug. Recorded because the difference between the two
readings is invisible in the output.

### 1.3 What the sizing does NOT say

Applicability is not decidability. 111 of 116 files CAN emit an order lemma;
ADR-2112 §D measured z3's own order class as load-bearing on 3 of 75 files it
decides. The sizing says the class is not structurally inapplicable to this
corpus — which was a live possibility, since 42 of the 116 never reach
`cas-ideal-refuter` at all — and it says the emission must be model-driven and
capped. It is the denominator for §4's A/B, not a prediction of it.
