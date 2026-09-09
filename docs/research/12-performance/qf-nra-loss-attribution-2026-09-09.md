# QF_NRA: where the 75 parity losses actually go — 2026-09-09

`QF_NRA` became the largest single division gap after the 2026-09-08 loss
re-cut (75 files, `bench-results/parity-losses-20260908/QF_NRA.txt`), and no
lane had looked at it. This note is the attribution sweep and what it found.

**Protocol.** The 75 files through `smtcomp_cli --trace` at the parity protocol
— 24 s wall, 8 GiB (`ulimit -v`), `taskset -c 0-7`, serial — via
`scripts/trace-sweep.sh`, classified by `scripts/nra-loss-classify.py`.
Total wall clock 752 s.

**The machine was not idle.** Load average moved between 0.7 and 8.7 during the
sweep (other lanes on the same box). Wall-clock numbers below are therefore
reported as *what a route consumed relative to its own budget*, and the
conclusions rest on decided counts, route identity and the loop's own counters
— not on absolute seconds.

## Read this before quoting any number here

Three separate instruments disagreed about the same run, and each was wrong in
a way that would have produced a confident, false answer.

1. **The `; give-up` line names the outer wrapper, not the branch that
   returned — on 15 of 75 files.** When `dispatch_reduced`'s own deadline has
   passed it REPLACES the inner reason with `"preprocessed dispatch timeout
   after reduced solve"` (`auto.rs:2292`). Five `LassoRanker` files that gave up
   on a *cross-product admission* refusal (`184`, `524`, `883`, `1476`
   cross-products) all print that wrapper timeout instead.

2. **The route trail is blind on 21 of 75 files.** Their whole
   `; route-trail` is one entry — `fd:parse`, `attempts=1`, `bound_ms=0`,
   `total_ms=0` — and they print no `; give-up` line at all, while the *same
   run's* `; lazy-smt` line on the same file reads `lra_entries=8
   lra_rounds=594 nra_entries=2 nra_rounds=2`. The work happened; the trail did
   not see it. Any "which route consumed the budget" table built from
   `bound_by` alone is therefore a statement about **54** of the 75 files, and
   the 21 it omits are not a random sample of them (they are the fast,
   theory-heavy `meti-tarski` end).

3. **The trail's literal last entry is not the reason either.** Every `fd:`
   attempt logged after a theory route copies that route's decline text
   verbatim, and `fd:parse` carries a probe note (`string_bound=12`) that is not
   a reason at all — reading it classified one file by the parser's probe
   string.

`scripts/nra-loss-classify.py` reads the last **non-front-door** route's detail,
falls back to the give-up line, and reports how often the two disagreed, for
exactly these reasons.

## The step-1 split

By the branch that returned (75 files, 752 s):

| class                                        | files | wall  | share |
|----------------------------------------------|------:|------:|------:|
| (c) size bound — `nra` atom capacity          |    14 | 276 s | 36.7% |
| (b) timeout — deadline inside a route         |     8 | 134 s | 17.8% |
| (b) timeout — watchdog kill                   |     3 |  75 s | 10.0% |
| (d) refinement reached a fixpoint             |    20 |  71 s |  9.5% |
| (d) no reason recorded (see hazard 2 above)   |    21 | 118 s | 15.7% |
| (d) other — FM elimination / generator caps   |     9 |  78 s | 10.3% |

On the budget axis, independently of the reason: **20 of 75 spend the whole
24 s**, 8 return near half of it, 10 return in under a second.

Three files that the census records as losses **decided** in this sweep (2 sat,
1 unsat). One is the known `QF_NRA.flaky.txt` entry; the other two are not, so
the loss list has at least three load-sensitive rows.

**The hypothesis this sweep was dispatched to test is false.**
`int_real_relax::refute_int_via_real_relaxation` — which held 24.7% of the
`QF_NIA` population's clock and refuted nothing — is unreachable here. It lives
in `dispatch_nonlinear_int_tail`, entered only when `features.has_int`, and
`QF_NRA` is real-only. It appears in no trail on any of the 75.

## What the loop's own counters say — the finding

`; lazy-smt` is present on **all 75** files (unlike the route trail), and it
splits each lazy-SMT round into the **propositional skeleton** solve and the
**theory** solve. Over the whole population: skeleton 191 s, theory 376 s.

The skeleton cost is not spread — it is concentrated. 16 files are
skeleton-dominated (≥ 50% of accounted time), and they hold 174 s of the 191 s.
Seven of them are one family:

| file (abbrev)                | rounds | `skeleton_ms` | `theory_ms` | skel% |
|------------------------------|-------:|--------------:|------------:|------:|
| `SantaBarbara01…Lasso_3`     |    290 |        23,769 |         163 |   99% |
| `polyrank4…Loop_2`           |    313 |        23,702 |         225 |   99% |
| `Brockschmidt…Fig1`          |    217 |        23,649 |         273 |   99% |
| `heidy7…Lasso_2`             |    217 |        23,620 |         271 |   99% |
| `InVarSynth_pcatest1`        |    150 |        23,587 |         297 |   98% |
| `eric2…Loop_3`               |    153 |        23,448 |         444 |   98% |
| `spiral…Loop_4`              |    119 |        23,224 |         544 |   97% |

**97–99% of a 24 s budget in the propositional half, ~1% in the theory.** These
are the `LassoRanker` ranking-function templates: heavy Boolean structure over
nonlinear atoms, and the exact CAD decides each individual cube in about a
millisecond.

### Why the skeleton is expensive, and why that is ours

The skeleton **never changes between rounds**. `dpll_t.rs` builds
`skeleton.clone() + blocking` afresh every round and hands it to a cold
`SatBvBackend`, so each round re-bit-blasts an identical formula and reruns CDCL
from scratch over a strictly larger clause set. The per-round histogram is
monotone in the round number — `polyrank4` reads
`nra_hist=2:3,3:12,4:23,5:34,6:61,7:118,8:62` with `nra_max_round=306`, i.e. the
first rounds cost ~4 ms and the last ~256 ms.

That is the signature of re-solving a growing formula from cold, not of a hard
propositional problem. The warm machinery for it already exists and is not new
work: ADR-0009's `IncrementalBvSolver` takes monotone assertions over a
persistent lowering and CNF encoding, which is exactly "assert the skeleton
once, add one blocking clause per round".

A second, independent weakness is visible in the same rows: the NRA loop blocks
the **whole cube** rather than a theory-unsat core (the LRA loop learns a Farkas
core; `dpll_t.rs` says so in a comment). That is the weakest learnable clause,
so the round count is as high as it can be. Nothing here measures how much a
core would buy; it is named as the next question, not as a claim.

## What this does not say

- It does not say the 16 skeleton-dominated files become wins. It says a
  quarter of the population's clock goes to work the engine repeats, and names
  the mechanism.
- The `(c) size bound` class — 14 files, the largest by wall clock — is
  *not* addressed by any of this. Those queries project to 36,945 / 26,296 /
  11,960 linear-real atoms against a consuming-engine capacity of 1,024
  (`lra_theory::MAX_ONLINE_LRA_ATOMS`), i.e. 11× to 36× past it. That is not a
  tuning distance. The decline text already says what it needs — an nlsat/CAD
  engine — and the `meti-tarski` shapes (a degree-6 univariate nonlinear atom
  coupled to two variables through *linear* atoms) are the canonical target for
  one.
