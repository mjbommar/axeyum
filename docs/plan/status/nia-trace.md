# Lane: nia-trace — what the QF_NIA clause estimate counts, and what z3 builds instead

<!-- plan-section: lane-status -->

**Lane nia-trace (`DONE`, nia-trace, 2026-09-15).** [ADR-2112] — `proposed`.
The question was why `QF_NIA` refuses ~42 files on
`estimated N CNF clauses before lowering exceeds budget 64000000` and what z3
builds instead. The answer moves the target: **z3 does not build a bit-blast on
this family either.**

**The census, all 116 undecided T1 rows, 8 widths each, 0 dropped.** The width
the query's VARIABLES need has median **2 bits**; the width its LITERALS force
has median **17**, and 30 files carry a literal needing 31–33. **95 of 115**
files have the first strictly below the second, and 29 have exactly ONE
admissible rung of the eight sampled. The mechanism is one line:
`encode_constant` (`int_blast.rs:603`) rejects the WHOLE blast when a single
literal falls outside the requested width's signed range, and `2^30 + 1` is a
Farkas-template *coefficient* over variables declared `-2 ≤ x ≤ 2`.

**The partition the ledger cannot show.** `dispatch_int_blast_width_ladder`
returns its LAST rung's `Unknown` (`auto.rs:11664`), so all 116 report the
width-32 estimate whatever happened below. Split by what actually bound them:
**44** of 115 have no admissible width whose estimate fits the cap; **69** had
one, so a real solve ran and returned `Unknown` on its own merits; 2 have no
admissible width at all. One sentence is reported for three causes.

**Estimate versus actual, on ten files rather than the one on record.** The
estimate over-approximates by **9.40x to 17.72x**, and every one of the ten
encodes to **6.1–8.4 M clauses against the 64 M cap that refused it**. The gate
is refusing an encoding that fits. **That does not license lifting it**: the
2026-08-21 diagnosis raised the ceiling to 600,000,000 — above every estimate
here — over all 49 files and decided **0**.

**What z3 does, with `file:line` on both sides.** `nla2bv_tactic.cpp:225` sizes
each integer variable from *its own* bounds (`log2(|up − low| + 1)`), defaults
to **4** bits for an unbounded one, and a large literal raises only that default
(`:289-298`) — never a bounded variable's width. The bit-vector holds the
OFFSET and the bound is added back in Int arithmetic (`:238-247`), so the
literal never enters the bit-vector; a product is then built at twice its
operands' own width (`bv2int_rewriter.cpp:376-417`). We give every integer
symbol one global width (`int_blast.rs:610-612`) forced up by the largest
literal. On the first undecided row **2,116 multiplier nodes are 99.5 % of the
estimate** — so our estimate is not loose about a circuit z3 also builds; it
counts a circuit z3 never constructs.

**And it does not matter, which is the finding.** Three z3 arms per file, back
to back on one pinned core, engine read from `-st` counters rather than from the
verdict: `qfnia` and z3's default strategy decide about two thirds of our
undecided rows, every one of them with `nlsat + grobner + horner + nla`
nonzero — and the **`nla2bv` bit-blast arm decides zero**. The `QF_NIA` gap is a
nonlinear-LEMMA gap, not a blasting gap. Four levers on the blasting side have
now been measured at zero decided files: the cap lift (0 of 49), the 32→64
width escalation ([ADR-1921], 0 of 110), the ladder reorder ([ADR-2106],
ceiling 3), and this lane's width floor.

**Shipped: the floor, DISARMED.** `AXEYUM_INT_BLAST_WIDTH_FLOOR=1` skips the
rungs the query's own literals have already decided against. It is wired and
reached — proved by setting it to a non-numeric value and watching
`config_lever.rs:124` panic — and worth nothing measurable, because the rungs it
removes are the ones that fail fastest by construction. The reachability control
is written to EXIT NONZERO on no movement, so "the lever is not worth anything"
is a reported failure and not a silence.

Soundness is not in the floor but under it, and the tests assert it rather than
assume it: a bounded-width bit-vector `unsat` is degraded to `Unknown`
(`lia.rs:96-107`) and a `sat` model is replayed against the exact integers, so
no width policy in this file can reach a wrong verdict.
`a_narrow_width_cannot_manufacture_an_unsat` checks both halves, with a positive
control at width 16 so the narrow `Unknown` is the bound speaking and not the
route being broken.

Mutation: `int-blast-width-floor`, **three mutations each killing EXACTLY ONE
named test, and no two the same one**, from a 4-test baseline;
`--check-anchors` `suites=141 anchors=1068 stale=0`.

Evidence, every per-row list and every script:
[`bench-results/nia-trace-20260915/`](../../../bench-results/nia-trace-20260915/README.md).

[ADR-2112]: ../../research/09-decisions/adr-2112-qf-nia-what-the-clause-estimate-counts.md
[ADR-2106]: ../../research/09-decisions/adr-2106-derived-ladder-order.md
[ADR-1921]: ../../research/09-decisions/adr-1921-the-int-blast-width-escalation-is-measured-and-not-shipped.md
