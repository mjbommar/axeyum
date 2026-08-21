# Where the QF_NIA deficit actually goes — measured findings

Status: **measurement-grounded diagnosis (2026-08-21).** Executes ranked gap #4
of the [2026-08-21 SMT capability gap
analysis](../../plan/gap-analysis-smt-solvers-2026-08-21.md) §9: *QF_NIA at
38.2 % of the reference — "the genuine multi-year catch-up".*

The brief was to test that framing rather than accept it, on the grounds that
three sibling rows had been mis-sized the same day. **The framing survives the
test — the three cheapest levers in the division yield 0, +1 and +3 files, and
that is reported below with the measurements that refute them — but two of its
premises do not.**

1. **cvc5 1.3.4 *is* on this host** (`/nas3/data/axeyum/harness/bin/cvc5`, not on
   `$PATH`), so this note is measured against the recorded reference itself, not
   a stand-in. Two documents — the brief for this task and the sibling
   linear-arithmetic note — state it is absent.
2. **z3 is not a stand-in for cvc5 here.** Same run, same window, same caps:
   z3 decides **136/200**, cvc5 **76/200**. The sibling note verified "z3 within
   5 files of cvc5" on four *linear* divisions and it holds there; on QF_NIA the
   two references are **60 files apart**, and cvc5's decided set is a strict
   subset of z3's.

And the sizing itself is not what the row says. **QF_NIA's deficit is one
benchmark family.** `20170427-VeryMax/ITS` is 134 of the 200 pinned files and
**74 of the 104 misses**. Excluding it, the same measurement gives 29/39 =
**74.4 % of cvc5** — around QF_RDL's rate. Including only it: 9/37 = **24.3 %**.

This is diagnosis, not construction. No shipped code changed. Three candidate
fixes were built in a private snapshot and measured; all three are reported with
their yields, and none is proposed for merge.

---

## 0. The instrument, and why you should believe it

Population: the **committed, pinned** competition list
`bench-results/parity-lists/QF_NIA.txt`, 200 files, sha256 `19b334d3b910` —
**identical to the hash recorded in the `PARITY.md` entry of 2026-08-06 this
row's 34/200 comes from**, so this is that population, not a re-sample.

Per file, three solvers, 24 s wall each, 12 GiB address-space cap, external kill
at 32 s (29 s for cvc5, matching `parity-run.sh`'s `budget + 5`):

- **axeyum** through `target/release/examples/uf_unknown_probe`, which calls the
  same `solve_smtlib` the shipped `smtcomp_cli` calls but prints the
  `UnknownReason` kind and detail the competition CLI must suppress.
- **cvc5 1.3.4** (`--tlimit=24000`) — the recorded reference, byte-identical
  version string to the `PARITY.md` entry: `cvc5 1.3.4 [git f3b21c4 on branch HEAD]`.
- **z3 4.13.3** (`/usr/bin/z3 -T:24`) — the second opinion, and here a very
  different one.

Route ladders come from a second pass: `explain_corpus --list … --json`.

**Every `file:line` in this note is as of `cb4a391c9`, the commit measured.**
Nothing on the solver path changed between that commit and the tip while this
note was written (checked: `git diff --name-only cb4a391c9..HEAD -- crates/`
touches three unrelated `examples/*.rs`).

### Five checks that this instrument is not lying

1. **It reproduces the recorded score, and slightly beats it.** This run decides
   **38/200** where the ledger entry records **34/200** at commit `a505e67e7`,
   15 days earlier. The direction matters: a contended sweep loses marginal
   files, so a run coming in *high* cannot be explained by load, and the +4 is
   ordinary progress since 2026-08-06.
2. **Zero disagreements, four ways.** Across the 200 files no decided verdict
   disagrees with any other decided verdict (axeyum/z3/cvc5) or with the
   benchmark's declared `:status`.
3. **The two axeyum instruments agree on the mechanism.** The front door
   attributes 106 failures to a budget timeout and 49 to an encoding-budget
   refusal; the independent `explain_corpus` route pass, run separately, reaches
   106 (102 + 4) and 47 on the same population.
4. **The protocol did not favour anyone.** No solver decided any file past the
   24 s budget: max decided wall is axeyum 18.1 s, cvc5 22.2 s, z3 22.5 s.
5. **The negative results are positive-controlled.** §1's zero for parse-level
   rejection is checked against a file the probe *does* reject
   (`error: parse error: unsupported: integer literal 1361129467683753853853498429727072845824 exceeds the modeled Int range`)
   and a well-formed file it does not.

**Reference frame.** 16-thread i5-12600K, sweeps at `-P 5`, load average 5–12
throughout, other lanes on the box. Wall times are an upper bound and decided
counts a lower bound.

**One number I cannot fully account for.** My cvc5 run decides 76/200 where the
ledger records 89/200. A deterministic sample of 20 of its 124 timeouts, re-run
**serially** on a quiet box (load 2.8), flipped **0**. So contention does not
obviously explain the 13-file shortfall and I am not claiming it does. It does
not affect the z3-vs-cvc5 comparison, which is internal to one run.

Raw per-file data and its column dictionary:
[`bench-results/nia-diagnosis-20260821/`](../../../bench-results/nia-diagnosis-20260821/README.md).

---

## 1. The failure taxonomy — 162 undecided files

Read off the `UnknownReason` the front door produced. `ref` is the sub-count a
reference (z3 or cvc5) decides and axeyum does not — the only files that
represent a deficit.

| class | meaning | files | median wall | budget used | ref |
|---|---|---:|---:|---:|---:|
| **T** `Timeout` | search ran out of wall clock | **106** | 24.1 s | 100 % | 69 |
| **S** `EncodingBudget` | a route refused on a projected-clause constant | **49** | 8.0 s | 33 % | 29 |
| **I** `Incomplete` | a route ran, converged on nothing, said so | 5 | 15.6 s | 65 % | 5 |
| **R** `ResourceLimit` | ingest decline: `distinct` with 16,525 arguments | 1 | 0.4 s | 2 % | 1 |
| **X** external kill | still running at 32 s (`mcm/106.smt2`) | 1 | 32.1 s | — | 0 |
| **P** parse-level rejection | — | **0** | — | — | — |

**P is a positive-controlled zero.** QF_UFLIA loses 26 files at the parser to
`Int` literals beyond `i128` (gap #4b); QF_NIA loses none. The same probe rejects
a 130-digit literal and an unknown operator when handed one, so the empty class
is a finding rather than an unasked question.

### The wall-clock question the brief asked

The sibling note's QF_UFLIA result was 48 files returning `unknown` after a
median **1.3 s of 24 s** — quitting at 5 % budget use. **The analogous class
here exists and is a third the shape.** 49 files quit at a median 8.0 s, which
is 33 % of the budget, not 5 %; the other 106 — two thirds of the deficit — run
the clock to the end. On the headline number: of the 104 files a reference
decides and we do not, **69 are full-budget searches and 29 are early declines.**

§4 measures all three of the obvious things to do about that. They yield 0, +1
and +3.

---

## 2. The route ladder — one route decides the whole division

`explain_corpus --list --json` over all 200 files. The ladder is strikingly
uniform:

```
[cas-identity-refuter] → [cas-int-units] → dl-online:NOT-APPLICABLE
  → lia-simplex:UNSUPPORTED → lia-dpll:UNSUPPORTED → nia-square:NOT-APPLICABLE
  → nia-linearize:DECLINE → nia-bounded-blast:NOT-APPLICABLE
  → [cas-ideal-refuter:INCOMPLETE] → int-blast-ladder            (decisive)
```

**The decisive (last) attempt is `int-blast-ladder` on 158 of the 161 traced
undecided files.** Every route specialised for nonlinear integer arithmetic
declines, and the division is decided — or not — by a *generic bounded integer
bit-blast*.

What each declines with, across the undecided set:

| route | decline | files |
|---|---|---:|
| `nia-bounded-blast` | `not-applicable` (no all-variables-bounded proof) | **158 / 158** |
| `nia-linearize` | `budget`: **lazy-LIA pre-SAT skeleton exceeds the joint resource boundary** | **107** |
| `nia-linearize` | `budget`: exhausted the timeout after *N* refinement rounds | 39 |
| `cas-ideal-refuter` | `incomplete`: nonlinear system exceeds the generator/atom/inequality ceilings | 100 |
| `int-blast-ladder` | `budget`: **wall-clock timeout reached** | 102 |
| `int-blast-ladder` | `budget`: **projected clause count exceeds 64,000,000** | 47 |
| `int-blast-ladder` | `incomplete`: constant does not fit width 32 / model overflowed | 5 |

`nia-linearize`'s 107 declines are on the **same constant the sibling note found
in QF_IDL** — `MAX_PRE_SAT_ARITH_ATOMS = 1_024` / `MAX_PRE_SAT_CNF_VARS = 4_096`
with a moderate envelope of `1_280`/`8_192` (`dpll_lia.rs:69-81`), against QF_NIA
skeletons carrying 1,500–12,000 atoms. That is now the second division where one
admission constant refuses the route that was built for the problem. §4.2
measures what happens when it is lifted.

### 2.1 The ladder has one live rung on a third of the list, and decides none of them

`dispatch_int_blast_width_ladder` (`auto.rs:5875-5943`) tries widths
`4,5,…,16,24,32`. A width is admissible only if **every integer constant in the
query fits it** — the rung returns `Incomplete: integer constant N does not fit
the bounded width w` before any search. So the number of usable rungs is set by
the single largest literal anywhere in the file:

| live rungs (of 15) | files | axeyum decides | rate |
|---:|---:|---:|---:|
| 0 | 4 | 0 | 0.0 % |
| **1** (width 32 only) | **28** | **0** | **0.0 %** |
| 2 (24, 32) | 45 | 7 | 15.6 % |
| 4–6 | 24 | 4 | 16.7 % |
| 7 | 98 | 26 | 26.5 % |
| 12 | 1 | 1 | 100 % |

**Zero of the 32 files with at most one live rung are decided.** 70 undecided
files have at most two, and a reference decides 47 of them.

The literal that does this is not a bound on the search space. Traced live on
`From_AProVE_2014__juHashMapCreateIsEmpty.jar-obl-10__p1784_safety_0.smt2`
(declared `sat`, z3 `sat` in 0.9 s), with the loop instrumented in a private
snapshot:

```
LADDER width=4  ms=1 -> Incomplete/integer constant -14 does not fit the bounded width 4
LADDER width=5  ms=1 -> Incomplete/integer constant 16 does not fit the bounded width 5
LADDER width=6  ms=1 -> Incomplete/integer constant 1073741825 does not fit the bounded width 6
…                                        (widths 7–24, identical, ~1 ms each)
ESTIMATE clauses=74329095 cap=64000000
LADDER width=32 -> refused: oversized encoding
```

`1073741825` is `2^30 + 1`. It appears **twice** in the file, as a *coefficient*:
`( * 1073741825 lam8n18 )`. It multiplies one Farkas multiplier inside a
ranking-function template whose interesting variables are declared
`( <= ( - 2 ) Nl4arg11 ) ( <= Nl4arg11 2 )` — a five-element domain. Fourteen of
the fifteen rungs are killed by a coefficient, and the fifteenth is refused by
the clause estimator.

### 2.2 The clause estimator over-approximates by 9.4×, measured

On that same file, instrumenting both sides of the gate in the snapshot:

```
ESTIMATE clauses=74329095   cap=64000000     ← pre-lowering, refuses
ACTUAL   vars=1807744  clauses=7917733       ← the encoding, once built
```

The real encoding is **8× under the ceiling it was refused by**. The source
already suspects this — `sat_bv_backend.rs:1833` says the estimate
"over-approximates by ~8x on multipliers" — but nothing had measured it against
this division, and §4.1 shows lifting the gate buys nothing anyway.

A sub-hypothesis I formed and **refuted**: that the over-approximation is
constant-operand multiplies, since `estimate_blast_clauses` charges every
`Op::BvMul` at `8w²` while `lower_mul_op` gates partial product `i` on `rhs[i]`
and the AIG folds `and(x, FALSE)`, so a constant multiplier with *k* set bits
emits *k* partial products. Implemented as a popcount-aware charge, it moved this
file's estimate 74,329,095 → 69,824,007 — **6 %**, not 9.4×. Constant multiplies
are not where the slack is. The finding survives; my explanation of it did not.

---

## 3. Hard for us, or hard for everyone? — and which reference are we scoring against

Same run, same window, same caps, all three solvers per file:

```
axeyum  38/200        cvc5  76/200        z3  136/200
```

| | files |
|---|---:|
| axeyum undecided | **162** |
| … a reference (either) decides | **104** |
| … **cvc5** decides | **49** |
| … **z3** decides | **104** |
| … **neither** decides — genuinely hard for everyone | **58** |
| axeyum decides, cvc5 does not | 11 |
| axeyum decides, **neither** reference does | 6 |

Two things follow and they point in opposite directions.

**The gap is real and it is not marginal slowness.** On the 104 files z3 decides
and we do not, z3's median wall is **2.1 s**: 31 under one second, 74 under five.
These are not instances it barely finishes.

**But 58 of our 162 failures are not a gap at all** — no reference on this host
decides them either, and 26 of those 58 carry `:status unknown` in the benchmark
itself. A deficit sized by "files we cannot decide" rather than "files the
reference decides and we do not" overstates this division by 36 %.

### 3.1 The reference choice moves the number by 60 files

`PARITY.md` scores QF_NIA against plain cvc5. On the linear divisions the
sibling note checked z3 against cvc5 and found them within 5 files, which is why
it used z3 freely. **That check does not transfer.** Here, on one run:

```
z3 136   cvc5 76   — and cvc5's decided set is a strict SUBSET of z3's
```

Not one file in 200 is decided by cvc5 and missed by z3. So "38.2 % of the
reference" is a ratio against a configuration that is 60 files weaker than
another reference sitting on the same disk, and the honest pair of numbers is:

| denominator | ratio |
|---|---|
| cvc5 1.3.4 plain, ledger 2026-08-06 | 34/89 = **38.2 %** |
| cvc5 1.3.4 plain, this run | 38/76 = **50.0 %** |
| **z3 4.13.3, this run** | 38/136 = **27.9 %** |

This is not an argument for changing the ledger's reference —
`scripts/parity-run.sh` picks cvc5 deliberately, and its header says why
(a *weaker* reference is the knob that flatters us; cvc5 was chosen because it
made other divisions harder). It is an argument that **on this division that
reasoning is inverted**, and the row should say which denominator it means.

### 3.2 The deficit is one benchmark family

| family | files | axeyum | z3 | cvc5 |
|---|---:|---:|---:|---:|
| **20170427-VeryMax/ITS** | **134** | **9** | 83 | 37 |
| AProVE | 19 | 15 | 19 | 17 |
| 20170427-VeryMax/CInteger | 15 | 2 | 12 | 3 |
| 20170427-VeryMax/SAT14 | 15 | 4 | 15 | 13 |
| **20220315-MathProblems** | 9 | **6** | **0** | **0** |
| 20210219-Dartagnan/ReachSafety-Loops | 3 | 0 | 3 | 3 |
| others (5 files) | 5 | 2 | 3 | 3 |

`VeryMax/ITS` is 67 % of the pinned list and **74 of the 104 misses**. Split the
list on it:

```
excluding VeryMax/ITS   (66 files)   axeyum 29   cvc5 39   z3 53    = 74.4% of cvc5
VeryMax/ITS alone      (134 files)   axeyum  9   cvc5 37   z3 83    = 24.3% of cvc5
```

74.4 % is around QF_RDL's rate and ahead of QF_LRA's. And on
`20220315-MathProblems` — number-theoretic identities — **we decide 6 of 9 and
both references decide 0**, which is what the CAS/ideal/square routes were built
for and where they work.

So "QF_NIA at 38.2 %" is not a statement about nonlinear integer arithmetic. It
is a statement about one generator's termination-proving output being two thirds
of the population that scores us. That population is a *choice*, exactly as gap
analysis §9 row 9 concluded for transcendentals — and unlike that row, this one
is a choice that is currently costing us the division's headline number.

### 3.3 What the family is, and why it is not a nonlinear-arithmetic problem

VeryMax files are Farkas-lemma ranking-function synthesis (`Target solver:
barcelogic`, per their own `:source`). The nonlinear products are
`template-coefficient × Farkas-multiplier`, the coefficients are declared into a
five-element box (`-2 ≤ Nl ≤ 2`), and the multipliers are `≥ 0` and unbounded.
The technique that decides them is a case split on the *narrow* factor, after
which every product is linear.

**Axeyum implements exactly that.** `nia_linearize::small_domain_lemmas`
(`nia_linearize.rs:750-777`) emits the exact split for a factor confined to a
width-`MAX_SMALL_DOMAIN_WIDTH = 4` interval — and `[-2, 2]` has width 4, at the
limit — and its own doc comment names the shape: *"the narrow factor is
typically a 0/1 template switch multiplying an unbounded multiplier"*. It is
unreachable on 107 of 160 files because `nia-linearize` is refused first, on the
`dpll_lia` pre-SAT envelope. §4.2 lifts that.

---

## 4. Three candidate fixes, built and measured

All three were built in a private snapshot (`scripts/lane-snapshot.sh`), never in
the shared tree, each behind a single environment knob so nothing else can
explain a delta. Each was positive-controlled first: the patched binary had to
*change behaviour* on a file whose baseline is known before any sweep was
believed.

### 4.1 REFUTED — "the encoding gate refuses queries that would encode fine"

The sharpest-looking lever in §2.2. The pre-lowering estimate over-approximates
by 9.4×, and 47 files are refused by it at a median 8.0 s with two thirds of the
budget unspent. `check_cnf_budgets` already re-checks the **real** clause count
after lowering, so the protection is not lost by loosening the projection.

Change: the pre-lowering ceiling `64,000,000` → `600,000,000` — 9.4× it, i.e.
the same *real*-clause protection at the measured over-approximation factor.

Positive control: on the §2.1 file the baseline prints
`EncodingBudget / estimated 74329095 … exceeds budget 64000000`; the patched
binary builds the encoding (`ACTUAL clauses=7917733`) and runs the SAT solver for
17.9 s. The route changed.

Result over all 49 `EncodingBudget` files, 24 s budget, 12 GiB address-space cap:

| outcome | files |
|---|---:|
| **newly decided** | **0** |
| now a full-budget timeout | 44 |
| killed at the external 32 s wall | 3 |
| still refused (estimate above 600 M) | 2 |
| memory abort | 0 |

Control: all **38** baseline-decided files re-run under the same patch stayed
decided, with **0** verdict changes.

**The refusal was hiding nothing.** Unlike QF_UFLIA's early quit, this one is in
front of a search that does not finish either. Note also what did *not* happen:
the sibling's §5.1 turned 71 clean `unknown`s into 54 memory aborts; here the
same shape of change produced none, because the post-lowering gate catches what
the projection let through. The lever is safe and useless.

### 4.2 REFUTED (+1) — "let `nia-linearize` run"

The route designed for this family, refused on 107 files by an admission
constant, with the exact case split of §3.3 sitting behind it.

Change: `exceeds_pre_sat_skeleton_boundary` (`dpll_lia.rs:1203-1208`) — all four
envelope constants scaled ×16, so 1,024/4,096 becomes 16,384/65,536.

Positive control: on the §2.1 file the baseline decline is
`pre-SAT skeleton exceeds the joint resource boundary (atoms=3495, cnf_vars=9475)`;
the patched binary instead reports
`exhausted the configured timeout after 51 rounds this solve`. The route ran.

Result over the **full 200-file list**:

| | baseline | patched |
|---|---:|---:|
| decided | 38 | **39** |
| gained | — | **1** (`SAT14/1623.smt2`, `sat` in 9.0 s; z3 agrees, declared `sat`, **cvc5 times out**) |
| lost | — | 0 |
| verdict disagreements | — | 0 |

**+1 of 200.** Traced on six of the newly-admitted files, `nia-linearize` runs
19–126 CEGAR refinement rounds and exhausts the budget on five of them. The
admission constant was not the binding constraint; the refinement loop's
convergence is.

### 4.3 The calibration: is the rest just slowness?

35 miss files — every third entry of the 104-file miss list, taken
deterministically, never chosen after seeing a result — re-run at **4× the
budget**, 96 s instead of 24 s.

| baseline class | files | newly decided at 4× |
|---|---:|---:|
| `Timeout` | 20 | **0** |
| `EncodingBudget` | 12 | **3** |
| `Incomplete` | 3 | 0 |
| **total** | **35** | **3** |

**Twenty of twenty `Timeout` files still time out at four times the clock.** The
T class is not one constant factor from finishing.

The three that decided are all from the S class and all took **21.0 / 34.4 /
40.1 s** — past the 24 s budget. That is a second, independent reading of §2.1:
their reported `EncodingBudget` was the *last rung's* refusal, not the reason
the query failed. `dispatch_int_blast_width_ladder` returns whichever `Unknown`
its final width produced, so on these files the consumer-visible reason names a
gate that was never the binding constraint.

---

## 5. The highest-leverage fix — a well-evidenced negative, and one thing worth building

**There is no cheap win in QF_NIA.** The three interventions above are the three
cheapest things available — the projected-encoding gate, the route-admission
envelope, and simply more clock — and they yield **0**, **+1** and **+3**. That
is the deliverable, and it is different in kind from the sibling row, where one
policy correction was worth +22 files.

The evidence that it is a capability gap and not a policy artifact:

- Every specialised nonlinear-integer route declines on essentially every file
  (§2), and the division is answered by a generic bit-blast.
- That bit-blast has **one live rung on 32 files and decides none of them**
  (§2.1), and the rung count is set by a coefficient rather than by the search
  space.
- Lifting the gate in front of the surviving rung produces **0** decides (§4.1).
- Admitting the route that was built for the family produces **+1** (§4.2), and
  when it runs it does 19–126 refinement rounds without converging.
- **4× the wall clock buys 0 of 20 T-class files** (§4.3).
- z3 decides 74 of the 104 misses in **under five seconds** (§3). We are not
  close and then losing on time; we are running a different algorithm.

So: the gap analysis's "genuine multi-year catch-up" is **confirmed for the
search**, and ranking QF_NIA last among decision work remains right.

**What is worth building is smaller than that, and it is not a search.** The one
place where the capability exists and does not fire is the eager small-domain
case split (§3.3): `small_domain_lemmas` is exactly the technique this family
needs, its width limit of 4 exactly matches the `[-2, 2]` boxes the benchmarks
declare, and it is reachable only through `nia-linearize`'s *lazy* refinement
loop, which is what fails. An **eager** pre-pass — split every product whose
narrow factor has an entailed width-≤4 box, then hand the resulting *linear*
integer problem to the LIA route — is a different route, not a constant, and it
would be measured against these 74 `VeryMax/ITS` misses. §4.2 does not price it:
raising the envelope admits the lazy loop, which is the thing that does not
converge. **This note does not claim that eager split works — only that it is
the one hypothesis left standing that the measurements above have not refuted,
and that it is bounded enough to A/B.**

### Ranked, with what each is worth

1. **Eager small-domain product split for QF_NIA** — addressable set 74
   `VeryMax/ITS` misses (30 of them cvc5-decidable). Unpriced; the mechanism is
   present and unreached. This is the next experiment, not the next build.
2. **Say which denominator the row means** (§3.1). Free. The division's ratio
   moves from 38.2 % to 27.9 % or 50 % depending on which reference is named,
   and both are currently unnamed in the row.
3. **Stop returning the last rung's `Unknown` from the width ladder**
   (`auto.rs:5939`). Not a decide-rate fix; it is why 47 files report a clause
   ceiling that §4.1 shows was never the binding constraint, and why three of
   them decide at 4× budget.
4. **Reconcile the ladder's constant-fit rule with what it is protecting**
   (§2.1). A coefficient forces width 32 and kills fourteen rungs, on files whose
   variables live in a five-element box. This is the same *shape* of finding as
   the sibling note's §3.2 (five routes, five unreconciled admission opinions).
5. **Do not build for `20220315-MathProblems`** — we are 6/9 there and both
   references are 0/9.

---

## 6. What this note does **not** establish

- **The 200-file list is 82 % VeryMax and 67 % one sub-family.** Every ratio here
  is a statement about that population. §3.2 splits it precisely for that reason.
- **My cvc5 run decides 76 where the ledger records 89**, and 0 of 20 timeouts
  re-checked serially flipped, so I cannot attribute the difference to
  contention. The z3-vs-cvc5 comparison is internal to one run and unaffected;
  the absolute cvc5 count should be treated as this run's, not as a correction
  to the ledger.
- **Nothing here has been through `scripts/parity-run.sh`**, which remains the
  only instrument allowed to move a `PARITY.md` number. The 38/200 above is a
  probe result, not a parity entry.
- **The A/B binaries were built from a private snapshot** at `cb4a391c9`, and
  neither patch is proposed for merge. §4.1's is refuted outright; §4.2's buys
  one file and its constants have measured justifications this note did not
  re-derive.
- **`explain_corpus` decided one file the front door did not**, consistent with
  its documented divergence. That is 0.6 % of the traced population; no
  `explain_corpus` verdict is used as an oracle anywhere here, and the route
  attribution is read off the routes that ran.
- **§5's eager-split proposal is unmeasured.** It is the residual hypothesis, not
  a result.
- **No claim is made about QF_NRA, QF_UFNIA, or the 1,101-file committed
  corpus**, none of which were measured.

## 7. Reproducing this

```sh
cargo build --release -q -p axeyum-bench --example uf_unknown_probe --example explain_corpus

# per-file front-door probe with the UnknownReason the competition CLI suppresses
( ulimit -s 524288; ulimit -v 12582912
  target/release/examples/uf_unknown_probe <file.smt2> 24000 )

# the references
/usr/bin/z3 -T:24 <file.smt2>
/nas3/data/axeyum/harness/bin/cvc5 --tlimit=24000 <file.smt2>

# route ladders
target/release/examples/explain_corpus --list bench-results/parity-lists/QF_NIA.txt 24000 --json
```

Data committed with this note, under
[`bench-results/nia-diagnosis-20260821/`](../../../bench-results/nia-diagnosis-20260821/README.md):

| file | contents |
|---|---|
| `QF_NIA.tsv` | 200 rows: axeyum verdict/`UnknownKind`/detail/wall, decisive route and its decline, z3 and cvc5 verdict and wall, declared `:status`, largest integer literal, live ladder rungs |
| `ab-clause-ceiling.tsv` | §4.1, 49 files |
| `ab-presat-envelope.tsv` | §4.2, the full 200-file A/B |
| `calibration-4x-budget.tsv` | §4.3, 35 files at 96 s |

## Provenance

Measured 2026-08-21 at `cb4a391c9`, 16-thread i5-12600K, z3 4.13.3 at
`/usr/bin/z3`, cvc5 1.3.4 at `/nas3/data/axeyum/harness/bin/cvc5`. Sweeps at
`-P 5`, A/B passes at `-P 4`–`-P 5`, load average 5–12 throughout. A/B binaries
built from a private `scripts/lane-snapshot.sh` tree; the shared checkout was
never modified.
