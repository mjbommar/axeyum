# ADR-2112: the QF_NIA clause estimate counts a circuit z3 never builds — and z3 does not decide these files by building one either

Status: proposed
Index-summary: PENDING — filled in when the reference sweep completes.
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

## Part A — the census: the literal forces the width, not the search space

`crates/axeyum-bench/examples/nia_estimate_census.rs` walks every undecided row
at eight widths. Evidence: `bench-results/nia-trace-20260915/`.

| | min | median | max |
|---|---:|---:|---:|
| `constant_width` — smallest width `blast_integers` will admit at all | 2 | **17** | 101 |
| `bound_width` — smallest width holding every VARIABLE's declared range | 2 | **2** | 33 |
| bounded symbols | 0 | 16 | 264 |
| unbounded symbols | 3 | 289 | 13,537 |

- **95 of 115** files have `bound_width < constant_width`.
- 108 of 115 need **three bits or fewer** for their variables; 30 carry a
  literal needing 31–33 bits and 28 more need 17.
- Sampling widths 4…32, **29 files have exactly ONE admissible rung** and 2
  have none.

The mechanism is one line: `encode_constant`
(`crates/axeyum-rewrite/src/int_blast.rs:603`) rejects the WHOLE blast with
`ConstantOutOfRange` when a single integer literal falls outside the requested
width's signed range. `1073741825 = 2^30 + 1` is a Farkas-template
*coefficient*; the variables it multiplies are declared `-2 ≤ x ≤ 2`, a
five-element domain. So the coefficient buys the width and the variables pay
for it, in `8·w²` gates per multiplier.

### A1 — the partition the ledger cannot show

`dispatch_int_blast_width_ladder` returns its **last** rung's `Unknown`
(`crates/axeyum-solver/src/auto.rs:11664`), so every one of these files reports
the width-32 estimate whatever happened below it. Splitting by what actually
bound them:

| | rows |
|---|---:|
| EVERY admissible width's estimate exceeds the 64 M cap | **44** of 115 |
| at least one admissible width fits — a real solve ran and returned `Unknown` | **69** of 115 |
| no admissible width at all | 2 of 115 |

The ledger reports the same sentence for all three groups. That is
[ADR-2060]'s defect one level deeper: not a reason word shared by two causes,
but a single *detail string* reported for a file the gate never bound.

### A2 — estimate versus actual, on ten files rather than one

The ten smallest of the 44, measured by lifting the pre-lowering gate
(`cnf_clause_budget = u64::MAX`) and stopping the search at zero conflicts, so
the number is the encoding and nothing else
(`estimate-vs-actual-10.tsv`):

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
encoding that does not fit; it is refusing one that does. The ratio is 9.40x to
17.72x and RISES with the estimate, so the single 9.4x reading recorded on one
file in [the 2026-08-21 diagnosis][diag] is the low end of the range, not a
constant.

### A3 — and that does not license tightening the estimate

Said here so the next lane does not spend the measurement again. [The
2026-08-21 diagnosis][diag] §4.1 raised the ceiling to **600,000,000** — above
every estimate in the table above — over all 49 `EncodingBudget` files:

| outcome | files |
|---|---:|
| **newly decided** | **0** |
| now a full-budget timeout | 44 |
| killed at the external wall | 3 |
| still refused | 2 |
| memory abort | 0 |

All 38 baseline decisions held, 0 verdict changes. The refusal stands in front
of a search that does not finish either. So the 11x over-charge is a real
defect in the **diagnosis** — it names a gate that is not the binding
constraint — and not, on this evidence, a route to a decided file.

## Part B — what z3 builds, and what our estimate counts that it does not

Two claims, each with `file:line` on both sides.

### B1 — the width comes from the variable's own bounds, not from the file's largest literal

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
`Sort::BitVec(self.width)` — one global width — and `encode_constant` (`:596-604`)
forces that width up to hold the largest literal or refuses the whole blast. No
bound is read anywhere on this path.

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
charges `8·w²` gates per `BvMul` at the node's result width
(`:2221`). On the first undecided row, **2,116 multiplier nodes contribute
43,335,680 of the 43,563,051 estimated gates — 99.5 % of the estimate.** Every
one of those multipliers is at a width set by a coefficient, over variables
that need three bits.

z3 never constructs those multipliers, for two independent reasons: the
variable is a 2–3-bit bit-vector rather than a 32-bit one, and the coefficient
is not in the bit-vector at all. So the answer is not that our estimate is
*loose* about a circuit z3 also builds — the existing `~8x` and `~3x` comments
(`sat_bv_backend.rs:2273`, `:2744`) say that, and §A2 measures it at 9.4–17.7x.
It is that the estimate is counting a **different circuit**: one our blaster
really would build, and one z3's never does.

## Part C — the finding that decides what to do next

**z3 does not decide this family by bit-blasting either.**

`bench-results/nia-trace-20260915/z3-engine-trace.sh` runs three arms per file,
back to back on the same pinned core, each with its own 24 s budget and 8 GiB
ceiling, with the engine read from `-st` counters rather than inferred from the
verdict (`test-stat-extraction.sh` is its control suite: nine checks, five
positive, two negative, one prefix-collision, one engine attribution on a
purely linear stat block that must come back `none`; it exits nonzero on any
failure).

PENDING — the full table lands with the completed sweep.

## Decision

PENDING.

## Consequences

PENDING.

[ADR-2060]: adr-2060-a-decline-reason-word-is-not-a-cause.md
[ADR-2106]: adr-2106-derived-ladder-order.md
[diag]: ../05-algorithms/nia-deficit-diagnosis-2026-08-21.md
