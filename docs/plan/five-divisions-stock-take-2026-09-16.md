# The five worst divisions, taken stock — 2026-09-16

The campaign the user opened on 2026-09-15 ("focus on improving these
divisions; trace our solver end to end and compare against z3, cvc5,
bitwuzla") ran nineteen lanes over two days and was paused on the afternoon of
2026-09-16. This is where it stands. The lane-by-lane record is in
[`status/coordinator-five-divisions-2026-09-15.md`](status/coordinator-five-divisions-2026-09-15.md);
every number below is copied from a lane's merged ADR or README, and the frame
is the 16-division board (200 files per division) plus the Tier 1 ledger sweep
on `db31113fa`, against z3 4.13.3 and cvc5 1.3.4 on the same lists. Bitwuzla
does neither arithmetic nor quantifiers and is not a reference here.

## The scoreboard

| division | 2026-09-15 | 2026-09-16 | best reference | gap |
|---|---:|---:|---:|---:|
| QF_NRA | 117 | **122** | z3 187 | 65 |
| QF_LRA | 107 | 107 | z3 166 | 59 |
| QF_NIA | 84 | 84 (**87** on the parity list after ADR-2142, see below) | z3 144 | 60 |
| UFLIA | 86 | 86 | z3 ∪ cvc5 144 (cvc5 alone 142, z3 139) | 58 |
| AUFDTLIRA | 119 | 119 | z3 176 | 57 |

**Addendum, 2026-09-17.** A regression in the native CDCL core's target-phase
snapshot (ADR-2142, found through Glaurung's warm-session timing) was fixed with
byte-identical search trajectories, and a 16-division board A/B of the fix
(`bench-results/board-ab-20260917-adr2142/`) moved **8 of 3,200 files, all
stable gains, 0 losses, 0 flips**: QF_UFLIA +5, QF_ABV +1, QF_BV +1, QF_NIA +1
(the parity-lists population; QF_NIA 86 → 87 there). Every parity number
quoted for those four divisions before 2026-09-17 undercounts by those
amounts; the five divisions above are otherwise unchanged, and QF_ABV's
decided files now run in half the time.

Nineteen lanes moved one division by five points (ADR-2121, ADR-2126). Two
more lanes hold measured gains that did not clear the ship bar:

- ADR-2134, the algebraic final coordinate: QF_NRA pinned **+4 stable, 0
  losses, 0 flips**; the held-out draw stopped at 23 of 200 when the campaign
  paused. One 60-minute run decides it.
- ADR-2136, order and monotonicity lemmas: **10 stable gains** (7 in UFNIA, 3
  in QF_NIA) against **3 stable losses** over 800 files, 0 flips. The losses
  are budget starvation of a later route, not lemma defects.

The ship criterion throughout was zero stable losses, zero sat/unsat flips, and
at least one stable gain on the pinned list AND a disjoint 200-file held-out
draw, every mover rechecked three times per arm. It refused one pinned gain
(ADR-2128, +4 pinned, −2 held-out), and that refusal was correct.

## What each gap is, now, at a file and line

Monday's table said "z3 does CAD" and "aborts". Every gap now names a
mechanism with an A/B behind it, and the hypotheses that were wrong are gone:
the dense tableau, the atom-count screen, the Gröbner gate, the bit-blast arm,
trigger selection, the macro finder, warm bases, bound propagation, and
quantifier activation on its own were each built or measured and were null or
necessary-but-not-sufficient.

- **QF_LRA is three defects, not a missing construct.** The refusal string
  "arithmetic outside the incremental engine" is false on all 47 files that
  lose on it (0 unsupported atoms). 27 have no tableau because admission still
  counts dense cells (`lra_online.rs:1308`, `simplex.rs:2090`) over the
  storage ADR-2111 made sparse, so the model falls to Fourier–Motzkin and
  declines; 11 are disequalities dropped at `lra_online.rs:2610` under a
  comment that is true of the offline driver and false of the CDCL(T) one,
  where z3 splits eagerly (`arith_eq_adapter.cpp:208`) and cvc5 on the model
  (`theory_arith_private.cpp:4271`); 7 are a deadline poll at pivot zero
  (`simplex.rs:1441`) wearing an incompleteness label.
- **QF_NRA is the CAD theory's sample point.** The Boolean clause loop is
  certified and null (0/0/0 on 800 files); 10 of its 16 admissible files are
  refused by the single-cell theory itself. The algebraic witness is the last
  cheap increment before projection.
- **QF_NIA is z3's lemma portfolio.** No single class is load-bearing on
  fifteen or more files; the two classes we lacked are worth ten files when
  they get budget without starving the route behind them. 67 of 116
  undecided rows never reach any lemma because the linear relaxation itself
  times out; that is the harder ceiling.
- **UFLIA and AUFDTLIRA are instance reach.** We find 98 % of z3's terms and
  discard the instances. Of z3's 1,025 proof instances over 53 cores, 46 % are
  nested instantiations, 36 % never match, 17 % match and are rejected, and
  ADR-2120's activation lever (built, OFF) recovers 102 of the 169 rejected.
  The discard sits in one place: `PositiveContext` is forced to `None` on
  entering a `forall` body (`qinst_egraph.rs:1948`) before any lever level is
  consulted, so no activation reaches a universal nested inside another
  binder. z3 and cvc5 both get this for free by asserting the instance back
  into the SAT layer (`smt_context.cpp:1482`, `theory_quantifiers.cpp:173`).
  Ground closure, arithmetic hosting and generation are each built and each
  necessary.

## What the two days bought besides five points

- **Two latent soundness bugs found by lanes building something else**:
  `RealAlgebraic::sign_at` read two endpoint samples as an enclosure and
  returned a wrong sign (fixed with an exact Sturm count; no shipped wrong
  verdict found), and the shipped cell checker rejected `x > 1 ∧ x < 0` (two
  false-reject bugs, fixed). A confounded A/B arm (`clause-loop` rebased onto
  `single-cell-sat` after the default moved) would have printed clean numbers.
- **The measurement discipline is the default**: one binary at two
  environment values, interleaved per file on a pinned physical core, three
  rechecks per arm, a disjoint held-out draw, `:status` compared on every
  verdict (0 disagreements over every sweep this campaign ran).
- **Instruments that were wrong were caught by measurement**: a census that
  predicted 1 of 4 movers (a first-wins decline slot), 13 of 71 `file:line`
  citations wrong on first check (now held by two exit-status checkers), two
  compute hosts whose `date` prints nanoseconds under a millisecond header.
- **The push hook names its failures** (ERR trap, per-step timing, xtrace on
  failure), and the five "silent" battery deaths were the coordinator's own
  `ulimit -v`.

## What the premise got wrong

The plan's premise was one named mechanism per division. It held for QF_NRA
and is holding for QF_LRA. It does not hold for QF_NIA or the quantified
divisions, where z3's edge is depth and plumbing rather than a trick, and each
lever we build is real but moves nothing alone. The composition of levers is
the untested hypothesis; its noise floor is ±1 on 53 cores (the three ADRs'
OFF arms read 15, 15 and 16), so a composition sweep needs a threshold before
it means anything.

Two process corrections: the baseline ledger is 313 commits behind head, so the
next campaign starts by re-measuring the board; and a lane that reports checks
as NOT RUN has predicted a red, so those checks run on its branch before the
merge (one stale fuzz premise sat red on main for 40 minutes).

## The resume queue, ranked

1. ~~**Finish ADR-2134's held-out draw**~~ Done 2026-09-17
   (`bench-results/nra-algebraic-witness-heldout-20260917/`): pinned +4 stable
   held, held-out 109 → 109 with zero movers, so the criterion's gain clause
   failed and the lever stays OFF. The four pinned gains are one benchmark
   family (`meti-tarski/atan/problem/2`); the held-out draw does not contain
   the shape.
2. **QF_LRA admission currency** (27 files): admit the online tableau on
   nonzeros, the currency the cube decider already uses (`lra_online.rs:2144`),
   not dense cells. Then **the disequality split lemma** (11 files): turn the
   replay-gate detection at `lra_theory.rs:498` into `(or (<= x y) (>= x y))`
   the way cvc5 does. Both mechanism-named, both small, both with the five
   LRA/DL/LIA z3 fuzzes mandatory.
3. **QF_NIA lemmas versus budget**: separate "emit the two lemma classes" from
   "widen `RefinementSetup::refine`'s slice"; the three losing files score it
   directly. On 0 stable losses, arm `AXEYUM_NIA_ORDER_LEMMAS`.
4. **Nested-binder activation** for UFLIA/AUFDTLIRA: two fixtures deciding
   whether a universal inside another binder can be activated at all, a
   per-core split of `inactive_dropped` into crossed-binder versus other, then
   the levers-composed sweep with a threshold above ±1. Largest gap, deepest
   work.
5. **Re-measure the board** on current head before any of the above is
   scored against it.

ADR numbers 2138 and 2139 were reserved by the last round and are unspent.
