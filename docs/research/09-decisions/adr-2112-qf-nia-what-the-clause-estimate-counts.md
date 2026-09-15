# ADR-2112: the QF_NIA clause estimate counts a circuit z3 never builds — and z3 does not decide these files by building one either

Status: proposed
Index-summary: The `QF_NIA` question was "why do we refuse ~42 files on `estimated 130191180 CNF clauses before lowering exceeds budget 64000000`, and what does z3 build instead". The answer moves the target off the blasting route entirely. **CENSUS**, all 116 undecided T1 rows at 8 widths, 0 dropped: the width a query's VARIABLES need has median **2 bits**, the width its LITERALS force has median **17**, and **95 of 115** files have the first strictly below the second — `encode_constant` (`int_blast.rs:603`) rejects the WHOLE blast when one literal overflows the requested width, so 29 files have exactly ONE admissible rung of eight sampled and 2 have none. **TWO CORRECTIONS TO ADR-2106, neither changing its numbers**: `dispatch_int_blast_width_ladder` returns its LAST rung's `Unknown` (`auto.rs:11664`), so the one sentence it bucketed is reported for THREE causes — 44 rows where no admissible width's estimate fits the cap, 69 where one does and a real solve ran and failed on its own merits, 2 with no admissible width; and the estimate/actual gap measured on TEN files rather than the one on record is **9.40x–17.72x**, with every one encoding to 6.1–8.4 M clauses against the 64 M cap that refused it. That does NOT license lifting the cap — raising it to 600 M was already measured at **0 of 49 decided**. **WHAT OUR ESTIMATE COUNTS**: `8·w²` per `BvMul` at a width a COEFFICIENT forced; on the first undecided row 2,116 multiplier nodes are **99.5 %** of the estimate. z3 never builds them — `nla2bv_tactic.cpp:225` sizes each variable from its OWN bounds (the base-2 log of its own range width, default 4), and `:238-247` keeps the bit-vector as an OFFSET so the literal never enters it at all. **AND IT DOES NOT MATTER**: three z3 arms per file, 24 s each, engine read from `-st` counters rather than the verdict, full coverage — `qfnia` decides **77 of 116**, default 76, and the `nla2bv` bit-blast arm decides **1**, on a file both other arms time out on (210 ms vs 24 s). `nlsat` conflicted on **67 of 76**; only 9 files are decided without it and 5 of those need nothing nonlinear. So the gap is a nonlinear-LEMMA and integer-CAD gap, not a blasting gap, and four blasting-side levers are now measured at zero decided files. Shipped DISARMED: an admissible-width floor, wired and reached (proved by a parse panic, not by a null) and worth **24.3 ms of 23,400** — 0.10 %, verdicts identical in all 7 paired runs. Mutation: three mutations, each killing EXACTLY ONE named test, no two the same.
Index-status: proposed
Date: 2026-09-15

## Context

`QF_NIA` is 59 behind on the pinned Tier 1 list: we decide **84 of 200**
(`bench-results/ledger/t1-QF_NIA-db31113fa.tsv`, 78 `sat` + 6 `unsat`), z3
4.13.3 decides 144 on the board list, cvc5 87.

[ADR-2106] sized a ladder-reorder against that gap and found the ceiling was
3 files, because **42 of the 47 candidate rows declined with
`estimated 130191180 CNF clauses before lowering exceeds budget 64000000`** — a
CNF-size refusal wearing the same `DeclineReason::Budget` word as a clock
expiry. It named the refusal; it did not ask what the refused number counts.

This ADR asks that, on all 116 undecided rows, and asks the paired question
nobody had asked: **what does z3 build instead?**

Evidence, every per-row list and every script:
[`bench-results/nia-trace-20260915/`](../../../bench-results/nia-trace-20260915/README.md).

## Part A — the census: the literal forces the width, not the search space

`crates/axeyum-bench/examples/nia_estimate_census.rs` walks every undecided row
at eight widths. 922 rows, **0 files over the memory ceiling, 0 dropped**. One
file (`array_3-1-O0.smt2`) takes the parser's word-only fallback and has no
flat view, so the shape columns cover 115.

| | min | median | max |
|---|---:|---:|---:|
| `constant_width` — smallest width `blast_integers` will admit at all | 2 | **17** | 101 |
| `bound_width` — smallest width holding every VARIABLE's declared range | 2 | **2** | 33 |
| bounded symbols | 0 | 16 | 264 |
| unbounded symbols | 3 | **289** | 13,537 |

- **95 of 115** files have `bound_width < constant_width`.
- 108 of 115 need **three bits or fewer** for their variables; 30 carry a
  literal needing 31–33 bits and 28 more need 17.
- Sampling widths 4…32, **29 files have exactly ONE admissible rung** and 2
  have none.

`bound_width` counts only symbols with a two-sided range stated in the query; a
symbol without one contributes nothing, so it is a LOWER bound on what a
per-variable policy would need and cannot overstate the gap.

The mechanism is one line: `encode_constant`
(`crates/axeyum-rewrite/src/int_blast.rs:603`) rejects the WHOLE blast with
`ConstantOutOfRange` when a single integer literal falls outside the requested
width's signed range. `1073741825 = 2^30 + 1` is a Farkas-template
*coefficient*; the variables it multiplies are declared `-2 ≤ x ≤ 2`, a
five-element domain. The coefficient buys the width and the variables pay for
it, in `8·w²` gates per multiplier.

### A1 — one sentence, three causes

`dispatch_int_blast_width_ladder` returns its **last** rung's `Unknown`
(`crates/axeyum-solver/src/auto.rs:11664`), so every one of these files reports
the width-32 estimate whatever happened below it:

| | rows |
|---|---:|
| EVERY admissible width's estimate exceeds the 64 M cap | **44** of 115 |
| at least one admissible width fits — a real solve ran and returned `Unknown` | **69** of 115 |
| no admissible width at all | 2 of 115 |

This is [ADR-2060]'s defect one level deeper than [ADR-2106] found it: not a
reason *word* shared by two causes, but a single *detail string* reported for a
file the gate it names never bound. **It does not change any number in
[ADR-2106]**, whose bucketing of 47 candidate rows is correct for what it
measured; it says that bucket is not a partition of causes.

### A2 — estimate versus actual, on ten files rather than one

The ten smallest of the 44, measured by lifting the pre-lowering gate
(`cnf_clause_budget = u64::MAX`) and stopping the search at zero conflicts, so
the number is the encoding and nothing else (`estimate-vs-actual-10.tsv`):

| estimate | actual | ratio |
|---:|---:|---:|
| 74,481,639 | 7,923,115 | 9.40x |
| 75,355,131 | 7,916,829 | 9.52x |
| 81,656,940 | 7,858,039 | 10.39x |
| 82,137,495 | 7,911,622 | 10.38x |
| 82,762,788 | 7,986,732 | 10.36x |
| 94,622,511 | 6,065,434 | 15.60x |
| 94,374,759 | 8,300,893 | 11.37x |
| 99,823,977 | 8,359,515 | 11.94x |
| 105,875,904 | 6,195,202 | 17.09x |
| 111,943,962 | 6,317,982 | 17.72x |

**Every one encodes to between 6.1 M and 8.4 M clauses — an order of magnitude
UNDER the 64 M cap that refused it.** The gate is not protecting against an
encoding that does not fit; it is refusing one that does. The ratio rises with
the estimate, so the single 9.4x reading recorded on one file in [the 2026-08-21
diagnosis][diag] is the low end of a range, not a constant.

### A3 — and that does not license tightening the estimate

Said here so the next lane does not spend the measurement again. [The
2026-08-21 diagnosis][diag] §4.1 raised the ceiling to **600,000,000** — above
every estimate in the table above — over all 49 `EncodingBudget` files:
**0 newly decided**, 44 became full-budget timeouts, 3 were killed at the
external wall, 2 stayed refused, **0 memory aborts**, and all 38 baseline
decisions held. The refusal stands in front of a search that does not finish
either. The 11x over-charge is a real defect in the **diagnosis** — it names a
gate that is not the binding constraint — and not a route to a decided file.

## Part B — what z3 builds, and what our estimate counts that it does not

### B1 — the width comes from the variable's own bounds, not the file's largest literal

**z3.** `nla2bv_tactic.cpp::add_int_var` (`:209-263`) reads each integer
variable's bounds from a `bound_manager` and sizes THAT variable:

```cpp
unsigned num_bits = m_num_bits;
if (up && low) {
    num_bits = log2(abs(*up - *low)+numeral(1));   // :225
}
else {
    set_satisfiability_preserving(false);           // :232
}
```

`-2 ≤ x ≤ 2` gives `log2(5) = 2` bits. The default `m_num_bits` is **4**
(`:79`, `:444`) and is used only for a variable with no bound. A large literal
raises that default (`update_num_bits`, `:289-298`) and therefore **never
touches a bounded variable's width**.

**Us.** `IntBlaster::blast_symbol`
(`crates/axeyum-rewrite/src/int_blast.rs:610-612`) gives every integer symbol
`Sort::BitVec(self.width)` — one global width — and `encode_constant`
(`:596-604`) forces that width up to hold the largest literal or refuses the
whole blast. No bound is read anywhere on this path.

### B2 — the literal never enters the bit-vector at all

**z3.** The bit-vector holds the OFFSET from the lower bound, and the bound is
added back in **integer** arithmetic (`nla2bv_tactic.cpp:238-247`):

```cpp
s_bv = m_bv.mk_ubv2int(s_bv);
if (low && !(*low).is_zero())
    s_bv = m_arith.mk_add(s_bv, m_arith.mk_numeral(*low, true));
```

A multiply is then built at **twice its operands' own width**
(`bv2int_rewriter.cpp::mk_bv_mul:376-417`): `align_sizes`, then
`mk_extend(n, …)` on both sides, capped at `max_bits` — and when the cap binds
it adds a `bvumul_no_ovfl` side condition (`:411-414`) instead of widening.
A 2-bit variable's product is a 4-bit multiplier.

**Us.** `encode_constant` (`int_blast.rs:601-603`) puts the literal's own bit
pattern into a `Sort::BitVec(width)` constant, so the literal's magnitude is
paid in the width of **every** term in the query.

### B3 — so: what does our estimate count that z3 does not build?

`estimate_blast_clauses` (`crates/axeyum-solver/src/sat_bv_backend.rs:2193`)
charges `8·w²` gates per `BvMul` at the node's result width (`:2221`). On the
first undecided row, **2,116 multiplier nodes contribute 43,335,680 of the
43,563,051 estimated gates — 99.5 % of the estimate.** Every one is at a width
set by a coefficient, over variables that need three bits.

z3 never constructs those multipliers, for two independent reasons: the
variable is a 2–3-bit bit-vector rather than a 32-bit one, and the coefficient
is not in the bit-vector at all. So the answer is not that our estimate is
*loose* about a circuit z3 also builds — the existing `~8x` and `~3x` comments
(`sat_bv_backend.rs:2273`, `:2744`) say that, and §A2 measures it at 9.4–17.7x.
It is that the estimate counts a **different circuit**: one our blaster really
would build, and one z3's never does.

## Part C — z3 does not decide this family by bit-blasting either

`bench-results/nia-trace-20260915/z3-engine-trace.sh` runs three arms per file,
back to back on the same pinned core, each with its own 24 s budget and 8 GiB
ceiling. The `engine` column is read from `-st` COUNTERS being nonzero, not
from a key being present and not from the verdict: every `QF_NIA` query runs
the SAT core and the linear arithmetic layer, so naming those says nothing.

All 116 undecided rows, full coverage on every arm:

| arm | what it runs | decided of 116 | sat | unsat | z3 median |
|---|---|---:|---:|---:|---:|
| `qfnia` | `(check-sat-using qfnia)` | **77** (66.4 %) | 40 | 37 | 1,309 ms |
| `default` | z3's own strategy | 76 (65.5 %) | 39 | 37 | 1,210 ms |
| `nla2bv` | `(then simplify nla2bv smt)` | **1** (0.9 %) | 1 | 0 | 210 ms |
| union | | 79 (68.1 %) | | | |

**`nla2bv` is the mechanism Part B is about, and it decides one file of 116.**
That file is worth naming rather than rounding away:
`20220315-MathProblems/STC_0078.smt2`, where z3's default strategy and its own
`qfnia` tactic **both time out at 24 s** and the explicit blast returns `sat` in
**210 ms**. So the honest ceiling for a bounds-derived per-variable width route
on this population is about **1 %**, not 0 — and it is a different 1 % from what
the lemma layer reaches.

Engines nonzero on `qfnia`'s 77 decided runs: `nlsat` 68, `nla` 67, `grobner`
62, `horner` 44; 8 decided with no nonlinear counter at all.

### C1 — the measurement boundary, stated because it bounds Part D

z3 pools basics, order, monotonicity and tangent lemmas into **one** counter,
`arith-nla-lemmas` (`src/math/lp/lp_settings.h:127`). A release z3 cannot
separate them, and `-v:10` does not either — it prints tactic progress, not
lemma classes; only a TRACE build would. So no claim here attributes a file to
`order` rather than `tangent` **from the counters**. Part D gets around this by
ablation rather than by counting.

### C2 — the counter cross-tab, and the partition with ADR-2110

Over the 78 files z3 decides (`z3-stats-78.tsv`; 76 re-decided in the capture
arm, the 2 that did not are kept visible rather than dropped):

| machinery | files with a conflict / firing | z3 median |
|---|---:|---:|
| monomial bounds (`nla_intervals.cpp`) | 67 of 76 (88.2 %) | 1,410 ms |
| `nlsat` (`src/nlsat/`) | **67 of 76 (88.2 %)** | 1,410 ms |
| nla lemmas (POOLED) | 66 of 76 (86.8 %) | 1,410 ms |
| Grobner (`nla_grobner.cpp`) | 61 of 76 (80.3 %) | 1,410 ms |
| int branch-and-bound | 44 of 76 (57.9 %) | 2,111 ms |
| Horner (`horner.cpp`) | 42 of 76 (55.3 %) | 1,860 ms |
| int cube/HNF | 39 of 76 (51.3 %) | 2,111 ms |
| int Gomory cuts | 30 of 76 (39.5 %) | 2,162 ms |

**`nlsat` conflicted on 67 of 76. Only 9 files are decided without it, and 5 of
those 9 need nothing nonlinear at all.**

That is the partition this ADR and ADR-2110 (lane NRA-TRACE, reading `nlsat`
for `QF_NRA`) divide the population on: the 67 are an integer-CAD question and
belong to that lane's subject; the 9 are what a lemma layer alone reaches, and
4 of them need any nonlinear machinery whatsoever.

## Part D — which class is LOAD-BEARING, by ablation rather than counting

PENDING — the ablation is running; its table lands here.

## Part E — our lemma inventory against z3's, with `file:line` on both sides

Reading the STEP rather than the name, because a name search does not find a
lemma family that is spelled differently.

| z3 class | z3 | ours | verdict |
|---|---|---|---|
| basics: sign / zero | `nla_basics_lemmas.cpp` | `sign_lemmas` (`nia_linearize.rs:110`) | **present** |
| monomial bounds / intervals | `nla_intervals.cpp` | `harvest_const_bounds` (`:587`) + `mccormick_lemmas` (`:724`) + `add_entailed_bound_lemmas` (`:1103`); `nra_fbbt.rs` on the Real side | **present, but see E1** |
| tangent lemmas | `nla_tangent_lemmas.cpp` | `tangent_lemmas` (`:1732`), `refine_with_tangents` (`:1772`) | **present** |
| Grobner basis | `nla_grobner.cpp` | `cas_ideal_refutation` (`cas_poly.rs:640`) → `unit_ideal_cofactors` (`:707`), cofactor-tracked with S-pair and basis-size ceilings | **present** |
| exact narrow-factor split | — | `small_domain_lemmas` (`:799`) | **ours only** |
| **order lemmas** | `nla_order_lemmas.cpp:286-310` | — | **ABSENT** |
| **monotonicity lemmas** | `nla_monotone_lemmas.cpp:61-82` | — | **ABSENT** |
| **Horner cross-nested forms** | `horner.cpp` | — (our "Horner" is univariate *evaluation*, `nia_square.rs:20`, a different thing) | **ABSENT** |
| integer CAD (`nlsat`) | `src/nlsat/` | `nra.rs` is Real-only; the int route declines "this needs a nlsat/CAD engine" | **ABSENT** — ADR-2110's subject |

### E1 — the two absent lemma classes, stated as design claims

**Claim 1 — order lemmas relate two products that SHARE a factor; we abstract
every product independently.** z3's `order::generate_ol`
(`nla_order_lemmas.cpp:286-310`) emits, for monics `ac` and `bc`:

```
c > 0 ∧ ac ≥ bc → a ≥ b        c < 0 ∧ ac ≥ bc → a ≤ b
c > 0 ∧ ac ≤ bc → a ≤ b        c < 0 ∧ ac ≤ bc → a ≥ b
```

Our linearizer replaces each product `a·b` by a **fresh independent variable**
`r` and adds only per-product lemmas — sign (`:110`), envelope (`:724`), narrow
split (`:799`), tangent (`:1732`). Nothing in `nia_linearize.rs` relates two
abstractions that share a factor. Confirmed by the step and not the name: the
file contains **no IR magnitude term at all** — all eight `abs` occurrences are
Rust `.abs()` on `i128` constants (`:487`, `:488`, `:609`, `:610`, `:687`,
`:1793`, `:1798`), and order and monotonicity lemmas are both stated on `|·|`.
A Farkas / ranking-template system, which is what 101 of these 110 files are, is
made of products sharing template coefficients.

**Claim 2 — z3's magnitude coupling is MODEL-driven; ours is BOUND-driven, and
this population is mostly unbounded.** z3's monotonicity lemma
(`nla_monotone_lemmas.cpp:61-82`, and its own comment at `:73-82`) is

```
/\_i |m[i]| >= |val(m[i])| => |m| >= |product_i val(m[i])|
   Example: x <= -2 & y >= 3 => x*y <= -6
```

— a cut generated **at the current assignment**, needing no static bound, fired
every round. Ours is `mccormick_lemmas` (`:724`), which by construction fires
only for products whose factors carry constant bounds **entailed by the
relaxation** (`harvest_const_bounds`, `:587`). Part A measured that population:
median **16 bounded symbols against 289 unbounded ones per file**. So our only
magnitude coupling is conditioned on exactly the minority of symbols this corpus
does not have.

## Decision

PENDING — lands with Part D.

## Consequences

PENDING — lands with Part D.

[ADR-2060]: adr-2060-the-give-up-variant-could-not-tell-six-gates-apart-and-nothing-asked-it-to.md
[ADR-2106]: adr-2106-derived-ladder-order.md

[diag]: ../05-algorithms/nia-deficit-diagnosis-2026-08-21.md
