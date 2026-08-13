# CAS/SMT arithmetic capability corpus — append-only lab notebook

Purpose: an **independent, honest** baseline measurement of where axeyum's
arithmetic reasoning fails today, recorded BEFORE a concurrent lane wires
`axeyum-cas` into `axeyum-solver`. The corpus must be able to *fail* the
change, not flatter it.

Machine: 4 cores (`nproc` = 4), shared with at least one other agent building
Rust and a remote solver job. **Every wall time recorded here is an UPPER
BOUND on the true single-tenant cost.** Never quote these as timings; quote
them as ceilings.

Convention: entries appended with a `date -Is` stamp. Corrections are appended
as NEW entries, never edited into old ones. Every command is recorded verbatim
with its verbatim output.

---

## 2026-08-12T21:11:29-04:00 — notebook opened

```sh
$ date -Is
2026-08-12T21:11:29-04:00
$ nproc
4
$ uptime
 21:11:29 up 23 days, 12:04,  2 users,  load average: 0.54, 0.54, 0.57
```

Repo state at the moment of opening:

```sh
$ git log -1 --format='%H%n%ci%n%s'
9f0f4ed005220b4985bf6edd97f052e3a4a19163
2026-08-12 20:32:15 -0400
merge origin/session/rado-claim-ledger-2026-08-12 into the proof lane
$ git rev-parse --abbrev-ref HEAD
session/rado-claim-ledger-2026-08-12
$ timeout 60 git status --porcelain
?? crates/axeyum-solver/tests/zz_cas_probe_tmp.rs
```

The single untracked file is the other lane's CAS probe. **BASELINE COMMIT =
`9f0f4ed005220b4985bf6edd97f052e3a4a19163`.**

### Methodological decision recorded BEFORE any measurement

The other lane edits `crates/axeyum-solver/` and `crates/axeyum-cas/` **in this
same checkout**. If I build my harness against the live working tree, my
"baseline" would silently absorb whatever their in-progress edit happens to be
at build time — which would destroy the entire point of the exercise.

Therefore: `git archive HEAD | tar -x` into the scratchpad, and build the
harness against **that frozen source tree**. Pure read; touches nothing in
`.git` and nothing another lane owns. The baseline is then reproducible from
the SHA alone.

Prior art read first (both in full):
`docs/plan/proof-approaches-2026-08-12/route-b/{LOG.md,REPORT.md}`, plus the
route-b harness at
`scratchpad/route-b/src/lib.rs` (the `Q`/`pose`/`Tally` helpers, which this
harness adapts and extends with full-trace recording and JSON output).

---

## 2026-08-12T21:34-04:00 — frozen baseline tree + independent ground truth FIRST

```sh
$ git archive 9f0f4ed005220b4985bf6edd97f052e3a4a19163 | tar -x -C $S/baseline-src
$ du -sh $S/baseline-src
525M	.../scratchpad/baseline-src
```

**Ground truth was written and run BEFORE the solver harness existed**, on
purpose: if the corpus's expected verdicts were derived from axeyum, the
measurement would be circular. `docs/plan/cas-smt-capability-2026-08-12/
ground_truth.py` calls nothing from this repo — plain Python big-integer
arithmetic only.

```sh
$ python3 ground_truth.py > ground_truth.out
EXIT=0
=== checked 91 claims, 0 failed ===
real	0m1.879s
```

93 corpus entries: 91 with a machine-checked expected verdict, 2 (`three-cubes-114`,
`three-cubes-390`) declared **OPEN** — no expected verdict, any decisive answer
is a bug or a research result.

### Self-audit of the ground truth, and what it forced me to fix

First draft had **nine checks that were tautological or possibly vacuous**, i.e.
they would have printed `OK` while checking nothing — precisely the failure mode
CLAUDE.md's "tools have lied more often than the solver has been weak" warns
about. Caught by re-reading my own predicates, and fixed before any solver ran:

- `C3 L1-cancel` was `all(t == a*q for ... for t in [a*q])` — true by
  construction. Replaced with an enumeration that *collects* the
  hypothesis-satisfying triples and asserts a nonzero count: now **1112 triples**.
- `C5 L2-positivity` — added the same non-vacuity count: **3422 pairs**.
- `C13 L6-bezout` — the hypothesis set is narrow (Bezout *and* `a | b*t`), so a
  generator bug could easily have made it vacuous. Now counts: **2012 tuples**.
- `D12/D14/D16/D20` were literally `ok(True, "...")` placeholders. Replaced with
  evaluated witnesses (e.g. D16: `2^4-1^4 = 15 != 16 = (2-1)(2+1)(4+1)+1`).
- `D17 id-congruence` was `all(x**3 == x**3 ...)`. Replaced with a real
  quantification over pairs restricted to `x == y`.
- `F1` iterated 2·10^6 values behind an `abs(x) < 100` filter — correct but
  absurd; simplified.

Recording this because the same class of defect in the *solver* harness would
silently inflate the baseline. The harness below therefore also prints a
per-query count and a non-empty route string for every entry.

---

## 2026-08-12T21:28-04:00 — harness built against the FROZEN tree

```sh
$ export CARGO_BUILD_JOBS=1
$ cd $S/cas-benchmark/harness && cargo build --release
    Finished `release` profile [optimized] target(s) in 5m 46s
real	5m46.776s
```

Cold build of the whole axeyum chain at `-j1` on a contended box. The harness's
`Cargo.toml` path deps point at `$S/baseline-src/crates/...` — the `git archive`
of `9f0f4ed`, NOT the live working tree. A second copy of the same `main.rs`
lives at `docs/plan/cas-smt-capability-2026-08-12/harness/`, whose `Cargo.toml`
points at `../../../../crates/...` (the live tree) so future re-runs measure
whatever is checked out. Both copies are byte-identical in `src/main.rs`.

`[workspace]` empty table in both, so `cargo test --workspace` / `scripts/check.sh`
never build it, and the repo root's `members` list is explicit (`crates/*`
enumerated), so nothing sweeps it in.

## 2026-08-12T21:34:19-04:00 — BASELINE RUN at 9f0f4ed

```sh
$ uptime
 21:34:16 up 23 days, 12:26,  2 users,  load average: 4.32, 2.43, 1.47
$ ./harness/target/release/cas-capability-corpus --json baseline-9f0f4ed.json
real	5m48.167s
```

Load average **4.32 on 4 cores at the moment the run started** — the box was
fully saturated by the other lane's build. Every wall time in
`baseline-9f0f4ed.out` is an upper bound; several are certainly inflated.

```
===================== SUMMARY =====================
    67  DECIDED-OK
     2  OPEN-STAYS-UNKNOWN
    11  UNDECIDED-EXPECTED
    13  UNDECIDED-GAP

  --- decided vs undecided, by axis ---
  axis A: decided  10   unknown   5
  axis B: decided   8   unknown   2
  axis C: decided  10   unknown   4
  axis D: decided  20   unknown   0
  axis F: decided  10   unknown   4
  axis G: decided   4   unknown  11
  axis H: decided   5   unknown   0

  --- deciding routes (count of queries each route decided) ---
     3  dl-online
     5  int-blast-ladder
    16  int-real-relax
     1  lia-diophantine
     1  lia-dpll
     5  lia-simplex
    32  nia-linearize
     2  nia-square
     2  uf-arithmetic

  ALARMS: 0   ANCHOR REGRESSIONS: 0   BAD MODEL REPLAYS: 0
```

**Zero wrong verdicts across 93 queries.** Every decided verdict agrees with the
independently established ground truth. Every failure is `unknown`.

### A suspicion I logged and then had to withdraw

Reading the tail of the run I saw `wit | a=0 b=0 t=0 x=0 y=0 px=0 py=0` printed
directly above `C13`, and for a few minutes believed `C2-mono-k2-no-gcd` (which
asserts `a>=2, b>=1, t>=1, y>=1`) had returned an all-zeros model — i.e. a
wrong `sat`. **It had not.** The line belongs to the *preceding* entry,
`C12-L5-distribute-ctrl`, whose assertions are `x=a*px`, `y=a*py`,
`x-y=b*t`, `b*t != a*(px-py)+1` — all satisfied by zeros (`0 != 1`). C2's actual
model is `a=2 b=2 t=1 N=4 z=2 x=4 y=2 px=2 py=1`, which I checked by hand:
`N=a*b=4`, `z=a*t=2`, `x=y+b*t=2+2=4`, `x<=N` (4<=4), `x=a*px` (4=2*2),
`y=a*py` (2=2*1). Genuine witness. Recorded because the misread came from my own
output format, not from the solver.

## 2026-08-12T21:41:47-04:00 — the alarm classifier is not vacuous

Every alarm counter read zero. Per this repo's own rule that a gate which never
fires proves nothing, I added `--selftest`: two deliberately mis-declared
queries whose true verdicts are trivial.

```sh
$ ./harness/target/release/cas-capability-corpus --selftest
=== harness self-test: the alarm classifier must FIRE ===
  SELFTEST-wrong-verdict     got verdict=unsat    status=ALARM-WRONG-VERDICT    want status=ALARM-WRONG-VERDICT    OK
  SELFTEST-open-decided      got verdict=sat      status=ALARM-OPEN-DECIDED     want status=ALARM-OPEN-DECIDED     OK
  self-test failures: 0
SELFTEST EXIT=0
```

Both alarm paths fire. The zeros in the baseline are real zeros.

## 2026-08-12T21:41:58-04:00 — are the 13 gaps budget-starved? NO.

Re-ran only the `UNDECIDED-GAP` entries at **6x budget** (60 s instead of 10 s).

```sh
$ ./harness/target/release/cas-capability-corpus --budget-scale 6 \
    --json gaps-6x-9f0f4ed.json --ids A1-unit-direct,A3-unit-neg,...
real	9m25.637s
    13  UNDECIDED-GAP
```

**13/13 still undecided at 6x.** Three of them decline in well under a second
and are budget-independent: `A14-mod-phrasing` 0.19 s, `F3-sum2sq-3` 0.07 s,
`G4-pell-square-d` 0.07 s. These are structural, not resource, failures.

### The mechanism, from the traces (verbatim)

Every single gap has the same signature:

```
probe: fragment {int}
 | dl-online: declined (not-applicable)
 | lia-simplex: declined (unsupported)
 | lia-dpll: declined (unsupported)
 | nia-square: declined (not-applicable)
 | nia-linearize: declined (verifier-rejected: relaxation model failed
     ground-evaluator replay against the originals)
 | nia-bounded-blast: declined (not-applicable)
 | int-blast-ladder: declined (incomplete: no model within the bounded integer
     width 32; widen the bound)          <- or: (budget: ... timeout reached)
```

So the gap is **not** "no route handles nonlinear integers". It is:
`nia-linearize` produces a candidate and then *rejects its own candidate* at its
verify-before-return step, which is sound and correct; the only remaining route
is `int-blast-ladder`, which is bounded at integer width 32. Nothing in the
current ladder can refute an unbounded-integer claim once `nia-linearize` bows
out.

Contrast, same axis, decided in 0.00 s:

```
A5-unit-signed  (a>=2 /\ p>=1 /\ a*p=1)   -> int-real-relax: decided unsat
A6-unit-product (a>=2 /\ b>=1 /\ (a*b)*p=1) -> nia-linearize: decided unsat
B3-inst-window  (r = a^2*(w-s), 1<=r<=a^2-1) -> nia-linearize: decided unsat
```

while `A1 (a>=2 /\ a*p=1)`, `B1 (M>=1 /\ 1<=M*c<=M-1)` time out. The *simpler*
query is the one that fails.

---

## 2026-08-12T22:08:44-04:00 — corpus + baseline COMMITTED

```sh
$ git add docs/plan/cas-smt-capability-2026-08-12/<10 files>
$ git commit -m "docs(plan): CAS/SMT arithmetic capability corpus + baseline at 9f0f4ed" \
    -- docs/plan/cas-smt-capability-2026-08-12/
$ git show --stat HEAD | tail
 10 files changed, 2938 insertions(+)
```

Commit `e930f2debfe506efefc82e115e710a199d0110bf`. Pathspec-only; verified with
`git show --stat`. The other lane's WIP (`crates/axeyum-solver/src/cas_certificate.rs`,
`cas_poly.rs`, both ` M`) is untouched — confirmed by `git status --porcelain`
before and after.

**BASELINE COMMIT OF RECORD: `9f0f4ed005220b4985bf6edd97f052e3a4a19163`.**

## 2026-08-12T22:09-04:00 — the CAS bridge landed; measuring the AFTER state

```sh
$ git log -3 --format='%H %ci %s'
175372bdc6f63fa9128359d16d81528fe6b74b20 2026-08-12 21:50:55 -0400 feat(cas): bridge axeyum-cas into the solver with two certified refutation routes
9f0f4ed005220b4985bf6edd97f052e3a4a19163 2026-08-12 20:32:15 -0400 merge origin/session/rado-claim-ledger-2026-08-12 into the proof lane
$ git merge-base --is-ancestor 9f0f4ed HEAD && echo YES
YES: baseline 9f0f4ed precedes HEAD
```

The working tree is DIRTY (`M cas_certificate.rs`, `M cas_poly.rs`) — the other
lane has further uncommitted work. So the after-measurement uses
`git archive 175372bdc` into `$S/after-src`, same discipline as the baseline.
What is measured is the **committed** commit, not somebody's editor buffer.

```sh
$ export CARGO_BUILD_JOBS=2
$ cd $S/cas-benchmark/harness-after && cargo build --release
    Finished `release` profile [optimized] target(s) in 4m 04s
$ ./harness-after/target/release/cas-capability-corpus --selftest
  SELFTEST-wrong-verdict  ... ALARM-WRONG-VERDICT   OK
  SELFTEST-open-decided   ... ALARM-OPEN-DECIDED    OK
SELFTEST EXIT=0
```

Self-test re-run on the AFTER binary too — the alarm classifier still fires, so
its zeros below are real zeros and not a broken classifier.

```sh
$ ./harness-after/target/release/cas-capability-corpus --json after-175372b.json
real	5m28.141s
    69  DECIDED-OK          (baseline 67)
     2  OPEN-STAYS-UNKNOWN  (baseline  2)
    11  UNDECIDED-EXPECTED  (baseline 11)
    11  UNDECIDED-GAP       (baseline 13)
  ALARMS: 0   ANCHOR REGRESSIONS: 0   BAD MODEL REPLAYS: 0
```

Per-query delta on the committed 93:

```
### VERDICT CHANGES
  A1-unit-direct   unknown(Timeout) -> unsat  | decl:int-blast-ladder -> cas-int-units  (10.00s -> 0.00s)
  A3-unit-neg      unknown(Timeout) -> unsat  | decl:int-blast-ladder -> cas-int-units  (10.00s -> 0.00s)
  total verdict changes: 2
### ROUTE CHANGES WITH SAME VERDICT (no capability delta)
  total re-attributions: 12   (D1 D3 D5 D7 D9 D11 D13 D15 D19 B9 -> cas-identity-refuter;
                               A5 A6 -> cas-int-units)
```

`cas-identity-refuter` decided 10 queries — **all 10 already decided at the
baseline**. Axis D was 20/20 before the change and is 20/20 after. On this
corpus the identity route contributes zero new decisions.

## 2026-08-12T22:20-04:00 — axis U: an adversarial probe of the NEW route

Two decided queries is a thin basis for a judgement, and a route that fires on
`a*p = 1` could be doing arithmetic or could be matching a shape. So I wrote
axis U **after** seeing the change, specifically to make it answer wrongly: ten
queries all carrying the syntactic shape `cas-int-units` fires on (product of
variables = small constant, under a lower bound), of which **six are
satisfiable**. Ground truth extended first (`101 claims, 0 failed`), then run
against BOTH binaries.

```
############ BASELINE 9f0f4ed — axis U ############   8 DECIDED-OK, 2 UNDECIDED-GAP
  U7-unit-minus-one      want=unsat  got=unknown(Timeout)  10.00s
  U9-three-factors-eq-1  want=unsat  got=unknown(Timeout)  10.00s
############ AFTER 175372bdc — axis U ############   10 DECIDED-OK, 0 gaps
  U1-unit-neg-p          want=unsat  got=unsat  0.00s  cas-int-units
  U2-product-eq-a        want=sat    got=sat    0.00s  nia-linearize
  U3-product-eq-0        want=sat    got=sat    0.00s  nia-linearize
  U4-unit-unbounded      want=sat    got=sat    0.00s  nia-linearize
  U5-two-factors-eq-1    want=unsat  got=unsat  0.00s  cas-int-units
  U6-two-factors-eq-4    want=sat    got=sat    0.00s  nia-linearize
  U7-unit-minus-one      want=unsat  got=unsat  0.00s  cas-int-units
  U8-product-eq-2        want=sat    got=sat    0.00s  nia-linearize
  U9-three-factors-eq-1  want=unsat  got=unsat  0.00s  cas-int-units
  U10-three-factors-eq-8 want=sat    got=sat    0.00s  nia-linearize
  ALARMS: 0
```

**The probe failed to break it, and that is the finding.** `cas-int-units` fired
on 8 queries across the full 103 and on **zero satisfiable ones**. It declines on
`a*p = 0`, `a*p = 2`, `a*p = a`, and the unbounded `a*p = 1` — each of which a
shape-matching implementation would have refuted. It is doing arithmetic.

## 2026-08-12T22:25-04:00 — combined verdict, 103 queries

```
                    baseline 9f0f4ed      after 175372bdc
  DECIDED-OK              75                    79      (+4)
  UNDECIDED-GAP           15                    11      (-4)
  UNDECIDED-EXPECTED      11                    11
  OPEN-STAYS-UNKNOWN       2                     2
  ALARMS / REGRESSIONS / BAD REPLAYS   0/0/0     0/0/0

NEWLY DECIDED: A1-unit-direct, A3-unit-neg, U7-unit-minus-one,
               U9-three-factors-eq-1  — all unsat, all cas-int-units, all
               10.00s unknown -> 0.00s
LOST (decided -> unknown): NONE
VERDICT FLIPS (sat <-> unsat): NONE
cas-* fired on any SAT-expected query: NO
```

No P0. Nothing that should be satisfiable returns `unsat`. Both OPEN entries
stay `unknown`. All four astronomical-witness tripwires stay `unknown` (the
correct conservative answer; `unsat` would have been the P0). All seven anchors
stay decided. All seven axis-F traps behave identically.

**Judgement: a genuine capability gain, correctly implemented, but narrow — and
not the gain the identity route was built for.** 4 of 103 queries move, all one
shape (`a·p = ±1`), which happens to be exactly the shape route B's report named
as the sharpest boundary of axeyum's arithmetic reach. `cas-identity-refuter`
adds zero new decisions because axis D was already saturated; its case has to
rest on certificate quality, not on capability, and this corpus cannot make that
case for it. The variable-divisor shape (`A9`, `A12`), the opaque window lemma
(`B1`, `B5`), and the whole monolithic-vs-decomposed axis (`C1`, `C7`, `C11`,
`C13`) are untouched — 11 structural gaps remain.

Not touched at any point in this session: `bench-results/frontier/*.json`.
`progress_frontier` was never run.
