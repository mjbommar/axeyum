# ADR-2112: the QF_NIA clause estimate counts a circuit z3 never builds — and z3 does not decide these files by building one either

Status: proposed
Index-summary: The `QF_NIA` question was "why do we refuse ~42 files on `estimated 130191180 CNF clauses before lowering exceeds budget 64000000`, and what does z3 build instead". The answer moves the target off the blasting route entirely. **CENSUS**, all 116 undecided T1 rows at 8 widths, 0 dropped: the width a query's VARIABLES need has median **2 bits**, the width its LITERALS force has median **17**, and **95 of 115** files have the first strictly below the second — `encode_constant` (`int_blast.rs:603`) rejects the WHOLE blast when one literal overflows the requested width, so 29 files have exactly ONE admissible rung of eight sampled and 2 have none. **TWO CORRECTIONS TO ADR-2106, neither changing its numbers**: `dispatch_int_blast_width_ladder` returns its LAST rung's `Unknown` (`auto.rs:11664`), so the one sentence it bucketed is reported for THREE causes — 44 rows where no admissible width's estimate fits the cap, 69 where one does and a real solve ran and failed on its own merits, 2 with no admissible width; and the estimate/actual gap measured on TEN files rather than the one on record is **9.40x–17.72x**, with every one encoding to 6.1–8.4 M clauses against the 64 M cap that refused it. That does NOT license lifting the cap — raising it to 600 M was already measured at **0 of 49 decided**. **WHAT OUR ESTIMATE COUNTS**: `8·w²` per `BvMul` at a width a COEFFICIENT forced; on the first undecided row 2,116 multiplier nodes are **99.5 %** of the estimate. z3 never builds them — `nla2bv_tactic.cpp:225` sizes each variable from its OWN bounds (the base-2 log of its own range width, default 4), and `:238-247` keeps the bit-vector as an OFFSET so the literal never enters it at all. **AND IT DOES NOT MATTER**: three z3 arms per file, 24 s each, engine read from `-st` counters rather than the verdict, full coverage — `qfnia` decides **77 of 116**, default 76, and the `nla2bv` bit-blast arm decides **1**, on a file both other arms time out on (210 ms vs 24 s). `nlsat` conflicted on **67 of 76**; only 9 files are decided without it and 5 of those need nothing nonlinear. **ABLATION, 78 files, 78-of-78 coverage on 8 arms, 75 baseline-decided: NO class reaches 15 and only `nlsat` reaches 5 (5 of 75, 6.7 %) -- against the 88.2 % of files its COUNTER conflicted on. 66 of 75 decide under EVERY single-class removal.** z3's advantage here is a redundant portfolio, not a class we lack, so no lemma prototype is built. Four blasting-side levers are now measured at zero decided files. Shipped DISARMED: an admissible-width floor, wired and reached (proved by a parse panic, not by a null) and worth **24.3 ms of 23,400** — 0.10 %, verdicts identical in all 7 paired runs. Mutation: three mutations, each killing EXACTLY ONE named test, no two the same.
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

§C2's counters say a machine produced a conflict. They do not say the file
needed it — z3 runs these as a portfolio, so "Grobner conflicted on 61 of 76"
is equally consistent with Grobner being load-bearing on 61 files and on none.
And §C1's pooling means the counters cannot separate order from tangent at all.

So: turn each class OFF and re-run. `z3-ablate-classes.sh` does that with
`smt.arith.nl.*`, eight arms per file including a `base` arm measured **in the
same sweep on the same core**, so a file the baseline misses is excluded from
every class rather than scored as a loss for all of them. Plain `(check-sat)`
and not the `qfnia` tactic, because the tactic builds its own pipeline and does
not route these parameters to the arithmetic solver; the script refuses to start
unless z3 accepts every switch, since an ignored switch would make every arm
equal the baseline and read exactly like "no class matters".

**DENOMINATOR: 75 files.** The sweep completed; the denominator is the files the
baseline itself decided — 78 reached, coverage 78 of 78 on every one of the
eight arms, and 75 of them baseline-decided.

| class disabled | files z3 stops deciding | z3's own file:line |
|---|---:|---|
| `no-nra` (nlsat) | **5 of 75** (6.7 %) | `src/nlsat/` |
| `no-tangents` | 3 of 75 (4.0 %) | `nla_tangent_lemmas.cpp` |
| `no-order` | 3 of 75 (4.0 %) | `nla_order_lemmas.cpp` |
| `no-grobner` | 3 of 75 (4.0 %) | `nla_grobner.cpp` |
| `no-horner` | 2 of 75 (2.7 %) | `horner.cpp` |
| `no-int-branching` | 1 of 75 (1.3 %) | int branch-and-bound |
| `no-cross-nested` | **0 of 75** | cross-nested consistency |

**No class reaches 15 files. Only one reaches 5.** The threshold this ADR was
conditioned on is not met by any absent class, and the honest answer is the
histogram rather than a prototype.

### D1 — the counters and the ablation disagree, and the ablation is right

`nlsat` **conflicted** on 67 of 76 (88.2 %) and is **load-bearing** on 5 of 75
(6.7 %). That gap is the whole reason this part exists: a conflict is not a
necessity, and a lane that had stopped at §C2 would have reported "the QF_NIA
gap is an integer-CAD gap" as a measured finding. It is not one.

### D2 — what z3 actually has here is REDUNDANCY, not a class we lack

| files broken by … | count |
|---|---:|
| **no single class removal at all** | **66 of 75** |
| exactly 1 class | 4 |
| exactly 2 classes | 4 |
| 5 classes | 1 |

**66 of 75 files decide under every single-class removal**, so only 9 of 75
depend on any one capability. z3's advantage on this population is not a lemma
family we are missing; it is that two or more independent routes reach the same
file, and knocking any one out leaves the others.

That reframes the gap and it is the finding with the longest reach here: a
single new lemma class, built to parity with z3's, would on this evidence move
**at most 5 files of 75** — and the three classes we lack score 3, 3 and 2.

### D3 — the honest limits of this table

- **75 files, and the per-class spread is 5/3/3/3/2/1/0.** At that denominator
  those are within one or two files of each other; the table supports "no class
  is large" and does NOT support ranking `no-nra` above `no-tangents`.
- The host carried other users' load (average 6.1) during the sweep. Both arms
  of a file run back to back on one pinned core so load largely cancels in the
  comparison, but a slower arm times out more, which can only INFLATE how
  load-bearing a class looks. The measured numbers are therefore upper bounds,
  which strengthens the conclusion rather than weakening it.
- Single-class removal does not measure a PAIR. A capability that only matters
  when another is also absent is invisible here.

## Part F — our Gröbner route is present, reached, and refused by its own ceiling

§E lists Gröbner as present, and it is: `cas_ideal_refutation`
(`cas_poly.rs:640`) routes into `unit_ideal_cofactors` (`:707`). Reading the
ledger rather than the source changes the picture:

| | rows |
|---|---:|
| trails that REACH `cas-ideal-refuter` | 115 of 200 |
| undecided rows that reach it | 75 of 116 |
| rows it DECIDES | **0** |

And its own recorded reason, over all 200 rows:

| decline detail | rows |
|---|---:|
| `nonlinear system exceeds the deterministic generator/atom/inequality ceilings` | **114** |
| `no combination of the asserted equations collapsed to a constant of the refuting sign` | 2 |

**The route is refused by its admission gate on 114 of 116 rows and actually
searches on 2.** The ceilings are `MAX_IDEAL_GENERATORS = 8`,
`MAX_IDEAL_INEQUALITIES = 8`, `MAX_IDEAL_ATOMS = 8`
(`cas_poly.rs:541`, `:555`, `:572`), tested as a hard early return at `:694-700`
against a corpus whose median file carries **342 integer symbols and 480
cross-products**.

The structural difference from z3 is the input, not the algorithm: ours takes
ALL top-level conjuncts at once (`top_conjuncts`, `:644`) and refuses if the
whole system is too big, whereas `nla_grobner` runs on a bounded slice of the
current simplex tableau (`grobner_row_length_limit` 10, `grobner_frequency` 4)
and is therefore small by construction however large the query is.

Three env levers already exist — `AXEYUM_MAX_IDEAL_GENERATORS`,
`AXEYUM_MAX_IDEAL_ATOMS`, `AXEYUM_MAX_IDEAL_INEQUALITIES` (`:551`, `:565`,
`:582`) — and the step ceilings below them (`reduction_steps` 6,000,
`pair_iterations` 1,500, `basis_size` 32, `poly_terms` 256, `ideal_limits()`
`:587`) bound the Buchberger work, so raising the admission gate degrades to a
step-ceiling decline rather than a hang. **That probe was NOT run here** and is
named as the next lane's first experiment rather than claimed as a result. Part
D bounds what it can be worth: z3's own Gröbner is load-bearing on 3 of 75.

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

**1. No lever ships ON. This ADR is `proposed`.** The one lever it adds — the
admissible-width floor, `AXEYUM_INT_BLAST_WIDTH_FLOOR` — ships DISARMED, and
its own measurement is why: it is wired and reached (proved by setting it to a
non-numeric value and watching `config_lever.rs:124` panic, rather than by a
null result), and worth **24.3 ms against a ~23,400 ms budget — 0.10 %**, with
verdicts identical in all 7 paired runs. The rungs it removes are the ones that
fail FASTEST by construction: `ConstantOutOfRange` is raised inside
`blast_integers`, before any AIG, any CNF and any SAT call. That closes open
item 4 of [the 2026-08-21 diagnosis][diag] ("reconcile the ladder's constant-fit
rule with what it is protecting"), filed and never measured: the rule is
protecting nothing expensive.

**2. The blasting side of `QF_NIA` is closed, with four measurements.** The cap
lift (0 of 49), the 32→64 width escalation ([ADR-1921], 0 of 110), the ladder
reorder ([ADR-2106], ceiling 3), and this lane's width floor (0.10 % of the
clock). And Part C adds the reference-side reason they all return zero: z3's own
bounds-derived per-variable blast decides **1 of 116**. A future lane should not
re-open per-variable widths without first explaining why that 1 would become
many.

**3. Do NOT tighten the clause estimate or lift the cap.** §A2 measures the
over-approximation at 9.40x–17.72x and every refused encoding at 6.1–8.4 M
clauses against a 64 M cap, which looks like an invitation. §A3 is the refusal:
raising the ceiling to 600 M — above every estimate measured — decided **0 of
49**. The over-charge is a defect in the DIAGNOSIS, not a route to a decision.

**4. Do NOT build a single nonlinear lemma class on this evidence.** Part D's
threshold was "≥ 15 of the population"; the largest class scores **5 of 75** and
the three we lack score 3, 3 and 2. **66 of 75 files are decided by a redundant
portfolio and break under no single-class removal.** The next capability here is
not order lemmas or monotonicity lemmas; it is whatever produces a SECOND
independent route to files we already reach once.

**5. What the ADR does hand forward, in order.** (a) Part F's ideal-ceiling
probe — our Gröbner route is refused by an 8/8/8 admission gate on 114 of 116
rows and never searches; three env levers already exist and the step ceilings
below them bound the work, so it is a measurement and not a build. (b) Report
the ladder's BINDING constraint instead of its last rung's
(`auto.rs:11664`) — §A1 shows one sentence standing for three causes, and that
is what made ADR-2106's bucket read as a partition. (c) The 67 files where
`nlsat` conflicted are ADR-2110's population, not this one's; §D1 is the warning
that goes with them — the counter says 88.2 % and the ablation says 7.3 %.

## Gates, with counts

A count is given for every suite, because a feature-gated suite compiles to
nothing and exits 0 — the shape that left one gate inert for 15 days here. Two
of these were caught by that rule during this lane: a re-run that matched no
test printed `ok. 0 passed; 1830 filtered out`, and the first reference sweep
wrote 79 rows with every statistic column empty.

| gate | result |
|---|---|
| `cargo test -p axeyum-solver --features z3 --test qf_lia_differential_fuzz` | **4 passed, 0 failed** (22.16 s) |
| `--test nia_differential_fuzz` | **1 passed, 0 failed** (56.04 s) |
| `--test qf_nia_bounded_product_differential_fuzz` | **1 passed, 0 failed** (125.35 s) |
| `--test qf_nia_divmod_const_differential_fuzz` | **1 passed, 0 failed** (7.90 s) |
| `--test qf_nia_divmod_var_differential_fuzz` | **1 passed, 0 failed** (554.26 s) |
| `progress_frontier --features full -- --test-threads=1` | **12 passed, 0 failed**; `comparable: true, ratchetable: true` on all five families, `nia_unsat` holding `baseline 40 / frontier 40` |
| `config_registry::tests` | **18 passed, 0 failed** |
| `auto::tests` for this lever | **6 passed, 0 failed** |
| mutation `int-blast-width-floor` | 4-test baseline green; **3 mutations, each killing exactly ONE named test, no two the same**; `--check-anchors` `suites=141 anchors=1068 stale=0` |
| clippy `-p axeyum-solver -p axeyum-bench -p axeyum-bv --all-targets --features full -- -D warnings` | clean |
| `cargo check --workspace --all-targets` (default features) | clean |
| `cargo fmt --all --check` | clean |
| `check-merge-hygiene.sh` / `check-links.sh` / `gen-plan.py --check` | PASS / ok / current |
| `check-config-registry-staleness.py` | 0 unexplained |

The last two `divmod` rows are the seed classes `CLAUDE.md`'s hard rule asks
for on an underspecified operator — a fuzz that never emits the degenerate
divisor is not a soundness gate, and `div`/`mod` by a **constant** zero is the
exact shape behind the wrong-unsat in `a946f925`.

`cargo test -p axeyum-solver --lib --features full` reported **1828 passed, 2
failed**, and neither failure is this lane's: both are wall-clock-bounded tests
(5 s, and a documented ~50 s solve) that flaked with six other lanes building on
the box, both are recorded as flakes of exactly this shape by four prior lanes
([ADR-2055] names the first at load average 11.09 with `pathological_refusals`
reading 0), and re-run alone here with the lever explicitly unset **both pass**,
1 each. The floor cannot reach either: with the lever off
`apply_admissible_width_floor` returns the width sequence before doing any work.

## Consequences

**Easier.** `nia_estimate_census.rs` gives any lane the per-file integer shape,
per-width admissibility and estimate-vs-actual in one command, and
`z3-stat-capture.sh` keeps every `-st` key in long form so a new bucketing
question does not need a new sweep. `ab-run-env.sh` generalises the
one-binary interleaved A/B to a whole assignment list.

**Harder.** Nothing. The lever is disarmed and byte-identical to the shipped
ladder when unset; `the_floor_removes_only_inadmissible_rungs` asserts that.

**Revisited when.** If a second independent nonlinear route lands (Part F's
probe, or an integer CAD from ADR-2110), re-run `z3-ablate-classes.sh` — the
interesting number is whether our own portfolio develops the redundancy §D2
measures in z3's, not whether any one route got stronger.

**A gate that did not answer what it was asked**, recorded because this lane
relied on it once: `scripts/check-links.sh` extracts INLINE links only
(`grep -oP '\]\(\K[^)]+'`, line 27) and never reference-style definitions
`[X]: path`. It printed "all links ok" over a dangling `[ADR-2110]:` target
naming a file that does not exist. Every reference definition in both ADRs
touched here was then checked by hand: 3 of 3 in this one, 7 of 7 in
[ADR-2106].

[ADR-2060]: adr-2060-the-give-up-variant-could-not-tell-six-gates-apart-and-nothing-asked-it-to.md
[ADR-2106]: adr-2106-derived-ladder-order.md

[diag]: ../05-algorithms/nia-deficit-diagnosis-2026-08-21.md
[ADR-1921]: adr-1921-the-int-blast-width-escalation-is-measured-and-not-shipped.md
[ADR-2055]: adr-2055-the-tableau-is-the-memory-and-capping-it-costs-eighteen-clean-exits.md
