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

Detail moved to [`../notes/118-nia-diagnosis.md`](../notes/118-nia-diagnosis.md).

<!-- plan-section: landed-changes -->

| 2026-08-21 | `45587c513` | QF_NIA gap #4 diagnosed. "Multi-year catch-up" confirmed for the search — three cheapest levers yield 0 / +1 / +3 files, 4× clock buys 0 of 20 timeouts — and three premises corrected: **cvc5 is on this host** (`/nas3/data/axeyum/harness/bin/cvc5`, not on `$PATH`; two docs say otherwise), **z3 is 60 files from cvc5 here** (136 vs 76, cvc5's set a strict subset), and **the deficit is one family** (`VeryMax/ITS` = 74 of 104 misses; excluding it, 74.4 % of cvc5). `int-blast-ladder` decisive on 158/161; its constant-fit rule leaves **1 live rung on 32 files, 0 decided**. Four per-file passes committed. |
