# Lane: agent-nia-diagnosis — QF_NIA, the last unsized gap row

<!-- plan-section: lane-status -->

**Gap #4 diagnosed; "multi-year catch-up" confirmed for the search, and the
sizing corrected three ways (`DONE`, agent-nia-diagnosis, 2026-08-21).**
[Gap analysis](../gap-analysis-smt-solvers-2026-08-21.md) §9 row 4 →
[nia-deficit-diagnosis](../../research/05-algorithms/nia-deficit-diagnosis-2026-08-21.md).
Measured at `cb4a391c9` over the pinned 200-file list (sha256 `19b334d3b910`,
the hash in the `PARITY.md` entry), three solvers per file at 24 s.

The framing survives: the three cheapest levers in the division yield **0**,
**+1** and **+3** files, and 4× the wall clock buys **0 of 20** search timeouts.
Ranking QF_NIA last among decision work is right. Three premises around it do
not survive:

- **cvc5 1.3.4 is on this host** at `/nas3/data/axeyum/harness/bin/cvc5` — not on
  `$PATH`, which is why two documents record it as absent. It was reachable the
  whole time.
- **z3 is not a stand-in for cvc5 outside the linear divisions.** Same run:
  z3 **136/200**, cvc5 **76/200**, and cvc5's decided set is a strict *subset* of
  z3's. Row 1's "within 5 files" check is true where it was made and does not
  transfer. So "38.2 % of the reference" means plain cvc5; against z3, 27.9 %.
- **The deficit is one benchmark family.** `20170427-VeryMax/ITS` is 134 of the
  200 files and **74 of the 104 misses**. Excluding it: 29/39 = **74.4 % of
  cvc5**, around QF_RDL. On `20220315-MathProblems` we decide **6 of 9 and both
  references decide 0**.

Mechanism, and it rhymes with row 1's §3.2: every specialised nonlinear-integer
route declines, so `int-blast-ladder` — a *generic* bounded integer bit-blast —
is decisive on **158 of 161** undecided files. Its width ladder admits a rung
only if every integer **literal** fits, so a `2^30` Farkas coefficient kills 14
of 15 rungs. **32 files have one live rung and we decide zero of them.**

Two findings worth not re-deriving:

- **The projected-clause estimator over-approximates by 9.4×**, measured
  (74,329,095 projected against 7,917,733 actual on one file). Lifting the gate
  by exactly that factor decides **0 of 49** and causes **0** memory aborts — the
  refusal was in front of a search that does not finish either. My explanation of
  *where* the slack comes from (constant-operand multiplies) was also measured
  and **refuted**: a popcount-aware charge moves the estimate 6 %.
- **The technique this family needs is already implemented and unreached.**
  `nia_linearize::small_domain_lemmas` splits a product whose narrow factor has a
  width-≤4 box, which is exactly the `[-2, 2]` box these benchmarks declare — but
  it is reachable only through the *lazy* refinement loop, which runs 19–126
  rounds and times out when the admission envelope is lifted.

**Postscript.** The board was re-measured 127 s after this landed
(`5be2b296c`) and the row now reads **40.7 % (33/81)**. Three same-day cvc5
runs give **76 / 76 / 81** against the **89** recorded 15 days earlier — the 89
is the outlier, and every "N files behind" priced off it is a few files too
large. My 38 is five above both same-day parity runs and I did not measure why;
treat it as this instrument's count. Nothing in the diagnosis moves: the classes
are per-file properties of our own failures, and a five-file boundary shift moves
no class across a conclusion.

Next, if this is picked up: an **eager** small-domain split feeding the resulting
linear integer problem to the LIA route, measured against the 74 `VeryMax/ITS`
misses. It is the one hypothesis these measurements have not refuted; it is
unpriced, and it is a route, not a constant.

<!-- plan-section: landed-changes -->

| 2026-08-21 | `45587c513` | QF_NIA gap #4 diagnosed. "Multi-year catch-up" confirmed for the search — three cheapest levers yield 0 / +1 / +3 files, 4× clock buys 0 of 20 timeouts — and three premises corrected: **cvc5 is on this host** (`/nas3/data/axeyum/harness/bin/cvc5`, not on `$PATH`; two docs say otherwise), **z3 is 60 files from cvc5 here** (136 vs 76, cvc5's set a strict subset), and **the deficit is one family** (`VeryMax/ITS` = 74 of 104 misses; excluding it, 74.4 % of cvc5). `int-blast-ladder` decisive on 158/161; its constant-fit rule leaves **1 live rung on 32 files, 0 decided**. Four per-file passes committed. |
