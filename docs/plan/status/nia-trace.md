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
to back on one pinned core, full coverage on all 116, engine read from `-st`
counters rather than from the verdict: `qfnia` decides **77 of 116**, z3's
default 76 — and the **`nla2bv` bit-blast arm decides 1**, on
`20220315-MathProblems/STC_0078.smt2`, where both other arms time out at 24 s
and the blast returns `sat` in 210 ms. The ceiling for a bounds-derived
per-variable width route is therefore about 1 %, not 0, and it is a different
1 % from what the lemma layer reaches. Four blasting-side levers are now
measured at zero decided files: the cap lift (0 of 49), the 32→64 width
escalation ([ADR-1921], 0 of 110), the ladder reorder ([ADR-2106], ceiling 3),
and this lane's width floor.

**The counters said one thing and the ABLATION said another.** Disabling each
of z3's nonlinear classes in turn (`smt.arith.nl.*`, 8 arms per file, `base`
measured in the same sweep on the same core; denominator **75 files**, the
sweep completing at 78 files with 78-of-78 coverage on every arm):

| class disabled | z3 stops deciding |
|---|---:|
| `no-nra` (nlsat) | **5 of 75** |
| `no-tangents` / `no-order` / `no-grobner` | 3 of 75 each |
| `no-horner` | 2 of 75 |
| `no-int-branching` | 1 of 75 |
| `no-cross-nested` | 0 of 75 |

`nlsat` **conflicted** on 67 of 76 (88.2 %) and is **load-bearing** on 5 of 75
(6.7 %) — a conflict is not a necessity, and a lane stopping at the counters
would have filed "the gap is integer CAD" as a measured finding. **No class
reaches 15; only one reaches 5.** And **66 of 75 files decide under EVERY
single-class removal**, so only 9 depend on any one capability: z3's advantage
here is a redundant portfolio, not a class we lack. A single new lemma class
built to parity would move at most 5 files of 75 on this evidence. The spread
(5/3/3/3/2/1/0) does not support ranking the classes against each other.

**One more thing the ledger says that the source does not.** Our Gröbner route
is present (`cas_ideal_refutation`, `cas_poly.rs:640`), is REACHED on 115 of
200 rows, and decides **0** — its admission gate (`MAX_IDEAL_*` = 8/8/8 at
`:541`/`:555`/`:572`) refuses **114 of 116** before it searches, against a
corpus whose median file carries 342 integer symbols and 480 cross-products.
Three env levers already exist and the step ceilings below them bound the work.
That probe is named as the next lane's first experiment and was NOT run here.

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

**The `--lib` sweep went red on two tests and neither is this lane's.**
1828 passed, 2 failed: `auto::tests::pathological_overbound_stays_terminal_under_every_policy`
and `euf_egraph::tests::check_qf_uf_with_config_is_bounded_by_timeout`. Both are
wall-clock-bounded (5 s and a documented ~50 s solve) and the sweep ran with six
other lanes building on the box. Both are documented flakes of exactly this
shape by four prior lanes — [ADR-2055] records the first "flaked once under load
average 11.09 (`pathological_refusals` read 0), passed alone", and ADR-1920 and
`uf-over-datatypes-2026-09-12` both record the second as "FAILED. Re-run alone it
passes". Re-run alone here with the lever explicitly unset, **both pass** —
1 passed each, nonzero counts confirmed, at 11.62 s and 353.35 s. The width
floor cannot reach either: with the lever off `apply_admissible_width_floor`
returns the width sequence before doing any work.

The first attempt at that re-run **ran zero tests** — `--exact` with a bare test
name matches nothing, and it printed `ok. 0 passed; 1830 filtered out`. It is
recorded rather than quietly fixed: that is the "green gate that checked
nothing" shape, and only printing the COUNT caught it.

**`progress_frontier` is green (12 passed, 0 failed) and its side effect was
NOT committed.** The run rewrites `bench-results/frontier/*.json` in place. The
enforced numbers held — `nia_unsat` stayed `baseline 40 / frontier 40`, the
family that regressed 17 points once — but `bv_reduction`'s recorded FRONTIER
high-water fell 39 → 33 while its baseline 30 held, so the ratchet passed and
the file still got worse. The cause is in the file: that run recorded
`load_start 7.10, load_end 8.30`. Committing it would have lowered another
family's recorded capability because this box was busy, which is the
"do not raise a baseline from an advisory run" rule pointing the other way.
The five JSONs are restored to `HEAD` and are not in this lane's commits.

Mutation: `int-blast-width-floor`, **three mutations each killing EXACTLY ONE
named test, and no two the same one**, from a 4-test baseline;
`--check-anchors` `suites=141 anchors=1068 stale=0`.

Evidence, every per-row list and every script:
[`bench-results/nia-trace-20260915/`](../../../bench-results/nia-trace-20260915/README.md).

[ADR-2112]: ../../research/09-decisions/adr-2112-qf-nia-what-the-clause-estimate-counts.md
[ADR-2106]: ../../research/09-decisions/adr-2106-derived-ladder-order.md
[ADR-1921]: ../../research/09-decisions/adr-1921-the-int-blast-width-escalation-is-measured-and-not-shipped.md
[ADR-2055]: ../../research/09-decisions/adr-2055-the-tableau-is-the-memory-and-capping-it-costs-eighteen-clean-exits.md
