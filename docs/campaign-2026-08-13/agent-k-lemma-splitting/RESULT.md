# agent-k — automatic hypothesis minimisation and lemma splitting

Landed: `19f4c769b` on `main`, `crates/axeyum-solver/src/hypothesis_min.rs`
(749 lines) plus five lines of `lib.rs` wiring. Gates green.

---

## Headline

Three things, in descending order of how much I would stake on them.

1. **The B4 boundary is characterised, and it is not hypothesis count.** Forty
   irrelevant degree-3 hypotheses cost 0.2 s and break nothing; **one** more
   hypothesis takes a 1 ms lemma to `unknown` at 1 s, 10 s, 60 s, 300 s and
   **1800 s**. The cause is `nra.rs:107` `MAX_CROSS_PRODUCTS = 2`, a
   deterministic admission cap that declines in **40 ms at every budget**. The
   register's "minimal hypotheses beat a bigger budget" is **correct**, and the
   answer to "budget or shape" is **shape**, with a mechanism and a constant.

2. **The minimiser recovers the human decomposition automatically.** On the
   route-B colour-1 hypothesis set, two goals that are `unknown` at 1800 s close
   in 2.1 s and 2.5 s with **exactly** the subsets the human found after four
   attempts and ~32 minutes.

3. **The `k = 3` obstacle moved and got smaller.** The "degree-3/4 inequalities
   in three variables" the campaign recorded as the blocker are proved in **2
   ms**. What actually stops it is integer rounding of a nonlinear bound, and
   the whole arithmetic core of the critical leaf discharges step-by-step in
   milliseconds once one product is abstracted. **`k = 3` is not proved** — the
   composition and twelve other leaves are unencoded — but the blocker now has a
   two-line reproduction instead of a paragraph.

**No minimised subset produced a wrong answer.** One was produced deliberately,
by deleting two guards at once, and is reproduced below.

---

## K1 — the curve

Harness: `artifacts/harness/k1` (detached workspace over a `git archive HEAD`
snapshot, built on disk per rule 7). Logs in `logs/`.

### Provenance, corrected first

The brief cites "the 2026-08-12 findings register, item B4". That row
(`docs/plan/findings-register-2026-08-12.md:35`) is `climb.py` hard-coding
`k = 4`. The measurement is a *different* file's B4,
`docs/plan/next-actions-from-the-rado-paper-2026-08-12.md:222-234`. And the
primary evidence — route-B's `.out` files and the binaries that made them — is
**not in the repository**; `docs/plan/proof-approaches-2026-08-12/route-b/`
holds `LOG.md` and `REPORT.md` and nothing else. Everything below is a
**re-encoding** from the notebook transcript, which quotes every lemma verbatim.

Also: `REPORT.md:98` says "All 8 attempts"; its own table at `REPORT.md:15` says
the monolithic run was 3 matched / **9** mismatched. The 8 is the *chain* run.

### Replication at HEAD (`logs/k1-replicate-10s.log`)

| lemma | 2026-08-12 | 2026-08-14 |
|---|---|---|
| M5, M6, M7, ASM, L1, L2, L4, L5 | 0.00 s unsat | unsat, 0.000-0.001 s |
| **L3** | unknown, 60 s | **unsat, 0.000 s** (`int-real-relax`) |
| **M8** (opaque `M`) | unknown, 45 s | **unknown**, 10 s |
| **L6** | unknown, 60 s | **unknown**, 10 s |
| MONO colour-1, CHAIN L3, CHAIN L5 (full `H`) | unknown | **unknown** |
| CHAIN T1, CHAIN TAIL (full `H`) | unknown | **unsat**, 0.013 s |

agent-i is right that `L3` in minimal form is decided today. But "any monolithic
query fails" is too strong: 3 of my 5 full-`H` chain goals are `unknown`, 2 are
not.

**The vacuity probe is the uncomfortable row.** `H` alone returns `unknown` at
10 s, and so does `H` minus `t=a*w`, which I expected to be `sat`. The solver
**cannot tell whether the hypothesis set is consistent** on this material. That
is the defect route-B hit at `LOG.md:509` (three controls that "could not
possibly return `sat`"), and it is why the minimiser's `Consistency` is
three-valued.

### Count is not the variable (`logs/k1-synth-curves.log`)

`L2` (3 hypotheses, 0.000 s) plus `n` logically irrelevant hypotheses, 5 s
budget:

| padding | n=0 | n=10 | n=20 | n=40 | boundary |
|---|---|---|---|---|---|
| disjoint linear | 0.001 s | 0.001 | 0.001 | 0.002 | **none** |
| disjoint degree 2 | 0.001 | 0.003 | 0.018 | 0.073 | **none** |
| disjoint degree 3 | 0.001 | 0.032 | 0.117 | 0.212 | **none** |
| coupled degree 2 | 0.001 | 0.044 | 0.136 | 0.263 | **none** |

A slope, not a cliff. Neither count, nor degree, nor variable-sharing.

### One hypothesis is the whole boundary (`logs/k1-leave-one-in-L3.log`)

`L3`'s minimal set `{a>=2, b>=1, t=a*w, w>=1}` plus exactly one other member of
`H`, 10 s:

| added | verdict |
|---|---|
| (none) | unsat 0.001 s |
| `x>=1`, `y>=1`, `t>=1`, `z=a*t`, `x=a*px`, `y=a*py` | **unsat 0.001 s** (6 of 10) |
| `bezout`, `x<=a*b`, `y<=a*b`, `x-y=b*t` | **unknown at 10 s** (4 of 10) |

### The mechanism, in the solver's own words (`logs/k1-real-probe.log`)

I first inferred from the route traces that `int-real-relax` was never reached —
it appears in the deciding traces and not the failing ones. **Reading the source
killed that inference**: `auto.rs:3865` records the route only on success, so a
decline is invisible. It runs every time.

Posing the same constraints over `Real` sorts, where the NRA engine gets the
whole clock instead of `int-real-relax`'s one-sixth share (`auto.rs:3778`):

```
L3 core           over Real -> Unsat   0.002 s   nra-real-root
L3 core + bezout  over Real -> Unknown 0.040 s   AT 1 s, 10 s, 60 s AND 300 s:
  "nonlinear abstraction: 4 cross-products exceed the deterministic
   admission bound of 2 (the multi-variable nonlinear case can OOM the
   relaxation; this needs a nlsat/CAD engine)"
```

`crates/axeyum-solver/src/nra.rs:107`, checked at `nra.rs:334`. **Budget-
independent**: 300 s buys the same answer as 1 s, in the same 40 ms.

Corroboration at scale, on s4/s5/s7 (`logs/ladder-*.log`): the full-`H` versions
of `L3`, `L5` and the monolithic case are `unknown` at 1 s, 10 s, 60 s, 300 s
and **1800 s**. The 7200 s rung was still running when this was written.

### The killer predicate (`logs/k1-monomial-probe.log`)

`L3` core plus one synthetic hypothesis:

| added | verdict |
|---|---|
| `q <= a*b`, `q <= a*c`, `q <= a*t`, `q <= b*t` (fresh `q`) | **unknown** |
| `a*u + b*v = 1` (goal variables) | **unknown** |
| `q = a*b`, `c*d = e`, `c*d + e*f = 1` | unsat 0.000-0.001 s |
| `q <= c*d`, `c*d >= 0` (all fresh) | unsat 0.000 s |
| `a*b >= 1` (goal monomial vs a constant) | unsat 0.001 s |

The property is **distinct normalized cross-product monomials in the goal's
connected component, after definitional elimination** — the counter is
`nra_real_root::normalized_cross_product_count` (`nra_real_root.rs:6017`), the
same one `nra.rs:334` gates on. It is a pure syntactic function, so the search
gets a free heuristic that predicts the cliff without a solver call.

### Answers to K1's three questions

- **Count / arity / degree / coupling?** None of them. It is the cross-product
  monomial count against a fixed cap of 2, and one hypothesis can carry it.
- **Budget or shape?** **Shape.** Measured at 1800x the default budget on three
  hosts, and the declining guard is a deterministic 40 ms check.
- **What does it spend the time on?** Not the deciding route. `int-real-relax`
  declines in ~40 ms and silently; the wall clock then goes to `nia-linearize`
  (18 rounds, 144 atoms, 313 bound lemmas) and `int-blast-ladder`, neither of
  which can decide it either.

---

## K2 — the minimiser

`crates/axeyum-solver/src/hypothesis_min.rs`. Public surface:
`minimize_hypotheses`, `split_goal_and_minimize`, `MinimizeConfig`,
`MinimizeOutcome`, `Consistency`.

**Greedy deletion cannot start.** `auto::unsat_core` (`auto.rs:658`) returns
`None` at line 664 unless the *full* set is already solver-`unsat`. Logically
`unsat` is monotone; the solver's `unsat` is not, and that non-monotonicity is
the phenomenon. So the search grows from below: subsets of ascending
cardinality, ordered by induced cross-product count, small per-probe budget
(250 ms — a sufficient subset closes in 1-2 ms, an insufficient one burns the
clock), then deletion-based shrink, which *is* valid once something has closed.

### What it closes that was `unknown` (`logs/k2-ab.log`)

Route-B colour-1 hypothesis set, 14 hypotheses. Monolithic at 10 s (and at
1800 s on the ladder hosts) versus the minimiser at its 250 ms default:

| goal | monolithic | minimised |
|---|---|---|
| `b*t >= a*b` (L3) | **unknown** | **CLOSED** `{a>=2, b>=1, t=a*w, w>=1}` — 2.5 s, 541 probes |
| `b*t = a*(px-py)` (L5) | **unknown** | **CLOSED** `{x-y=b*t, x=a*px, y=a*py}` — 2.1 s, 446 probes |
| `w >= 1` (T1) | unsat 0.010 s | CLOSED `{w>=1}` — 18 probes |
| `x-y <= a*b-1` (TAIL) | unsat 0.012 s | CLOSED `{x<=ab, y>=1}` — 66 probes |
| `a*b >= 1` (M5) | unsat 0.010 s | CLOSED `{a>=2, b>=1}` — 20 probes |
| `false` (whole colour-1 case) | unknown | **NOT FOUND** — 1471 probes |

Both closed subsets are *exactly* the ones route-B found by hand. Every result
carries `consistency = Consistent`, so none of them is vacuous.

**The `NOT FOUND` row is the honest scope boundary.** The monolithic colour-1
case needs a **chain** — intermediate lemmas nobody wrote down — not a subset of
what is present. Hypothesis minimisation solves one half of B4; the other half
is inventing `M1'`..`M7`, which is proof search.

### Soundness controls, and evidence each one fires

`artifacts/mutate.py`, log at `logs/mutation-matrix.log`. Guards deleted **one
at a time** (agent-i's lesson: stubbing the whole mechanism is a weak mutation).

| guard | tests killed |
|---|---|
| G-A vacuity | 2 |
| G-B re-verification | 1 *(0 on the first round — see below)* |
| G-C probe strictness (`Unsat` only) | 8 |
| G-D shrink strictness | 8 |
| G-E goal pin, search | 6 |
| G-F goal pin, verify | 6 |
| **G-G goal pin, shrink** | **0 — conservative, not load-bearing** |
| G-H cross-product ordering (a NON-guard, harness control) | 0, correctly |

**The first round measured G-B as a dud**: deleting the re-verification guard —
the one I would have called the most important — left all nine tests green,
because every other test's subset re-verifies trivially. Added
`re_verification_is_respected` (probe 5 s, verify 1 ns, expect `NotFound`); it
kills G-B and only G-B.

**G-G stays a measured dud and is recorded as conservative rather than shipped
as a control that cannot fire.** Whenever the un-pinned shrink would differ, the
surviving subset is inconsistent, which G-A already refuses. That is measured,
not argued: the paired deletion `G-A + G-G` kills exactly the same two tests as
`G-A` alone, so no forgery of G-G's shape exists while G-A is present.

### The deliberate wrong answer

`an_unentailed_goal_is_not_found_not_closed` survives every *single* deletion —
it is guarded in depth, not useless. Deleting **G-B and G-C together**:

```
an unentailed goal was reported closed:
  Closed { indices: [], consistency: Consistent, probes: 2 }
```

for `a>=2, b>=1 |- a*b >= 3`. Empty hypothesis set: the claim is that
`a*b >= 3` is a **tautology**. It is false at `a = 2, b = 1`. Two named guards
stand between that and a verdict, and the pair deletion is what it costs.

### The direction that is free, and the two that are not

Dropping hypotheses makes a goal *harder*, so `S ⊆ H` refuting means `H`
refutes. That never needs a guard. The two ways a minimiser is still a
wrong-answer generator:

* **dropping the goal** — made unrepresentable: the negated goal is a separate
  parameter, present in every probe (G-E/G-F);
* **a subset that closes because the hypotheses are contradictory** — a proof of
  everything, therefore of nothing (G-A). `Consistency` is three-valued because
  K1 measured that the solver frequently cannot decide it, and collapsing
  `Unknown` into `Consistent` would be the wrong-answer generator.

Determinism is a test (`minimisation_is_deterministic`), and no hash container
participates in any output.

### Gates

`cargo test -p axeyum-solver --lib --features full` = **1138 passed**
(1128 at HEAD + 10, nonzero and confirmed).
`scripts/check-fmt-complete.sh` = 883 files — **and I mutation-tested the gate**:
appending an unformatted line made it report
`1 file(s) not formatted: crates/axeyum-solver/src/hypothesis_min.rs`, so it
really examines the new file. `cargo clippy -p axeyum-solver --all-targets
--features full -- -D warnings` clean.

---

## K3 — the `k = 3` refutation

### A structural fact nobody had enumerated (`logs/k3-ground-truth.log`)

`artifacts/k3_ground_truth.py` re-derives the shell colouring from
`PROOF-BRIEF.md:20-38` and enumerates every monochromatic solution for
`2 <= a <= 7`, `b <= 9`, `gcd(a,b) = 1`, `N <= 3000`:

1. `b < a`: **solution-free in 17 of 17** pairs.
2. **Every defect, in every defective pair, sits in ONE leaf** — colour 2, `x`
   in the right shell, `y` in the left shell, `v(z) = 2`. Colour 1 and colour 3
   have **no** solutions at any tested `(a,b)`, on either side of `b = a`.

`LOG.md:671-673` budgeted "roughly 10 leaf cases". Only one of them can need
`b < a`. My leaf count (1 + 9 + 4) matches the notebook's own estimate exactly,
which is the cross-check that the reconstruction is faithful.

### The recorded blocker is not the blocker

`REPORT.md:86-88`: cases 2 and 3 need "degree-3/4 inequalities in three
variables". The critical leaf's closing inequality is exactly that:

```
a>=2, 1<=b<=a-1, a^3+a^2 <= a^2*b + 2*a*b  |= false    unsat  0.002 s
CONTROL  a>=2, b=a+1, same inequality                   sat    0.001 s
```

The control fires on precisely the `b = a+1` defect family. Degree and variable
count are not the obstacle.

### Where it does stop (`logs/k3-leaf.log`, `logs/k4-rounding.log`)

The leaf forces `s = a+1` from two bounds. Both bounding steps stall — and
minimisation cannot help, because the **minimal** form already fails:

```
a>=2, b>=1, a*b*s >= a^2*b + 1  |= s >= a+1     unknown 20 s   (3 hypotheses)
CONTROL: drop the +1                             sat     0.002 s
```

Posing the 24-hypothesis leaf and letting the minimiser at it returns
`NOT FOUND` at the 4000-probe cap on every chain goal — a red herring, as the
hand-derived minimal set shows.

**K4 localises it to two independent effects.**

| query | verdict |
|---|---|
| `s > a \|= s >= a+1` (pure LIA rounding) | unsat 0.000 s |
| `P>=1, P*s >= P+1 \|= s > 1` | unsat 0.000 s |
| `P>=1, P*s >= P+1 \|= s >= 2` (the two composed) | **unknown 1.5 s** |
| `P=6, P*s >= P+1 \|= s >= 2` (instantiated) | unsat 0.000 s |
| `P>=2, a>=2, P*s >= a*P+1 \|= s > a` | unsat 0.001 s |
| `Q=a*b, Q>=2, a>=2, Q*s >= a*Q+1 \|= s > a` | **unknown 20 s** |

Each half is microseconds; the composition is `unknown`. And `s >= 2` and
`s > 1` are the **same statement over the integers** — the verdict depends on
which side of the inequality the constant is written. Second effect: writing the
*definition* `Q = a*b` re-introduces the cross-products that abstraction removed.

### The arithmetic core does discharge, in pieces

Abstract `P := a*b` (sound: the conclusion needs only `P >= 2`), and every step
lands, each with a control where a control is meaningful:

| step | verdict |
|---|---|
| A `a>=2, b>=1 \|= a*b >= 2` | unsat 0.000 s |
| B `a*(a*b) = a^2*b` | unsat 0.000 s |
| C `P>=2, a>=2, P*s >= a*P+1 \|= s > a` | unsat 0.001 s (control **sat**) |
| D `s > a \|= s >= a+1` | unsat 0.000 s |
| E1 `P>=2, P*s <= a*P+2*P-1 \|= s < a+2` | unsat 0.001 s (control **sat**) |
| E2 `s < a+2 \|= s <= a+1` | unsat 0.000 s |
| F `a>=2, 1<=b<=a-1, s=a+1, z=a^2*s, z<=a^2*b+2*a*b \|= false` | unsat 0.002 s (control at `b=a+1` **sat**) |

`CHAIN E` unsplit (`|= s <= a+1`) is `unknown` at 20 s while `E1 + E2` are 1 ms —
the same `>=`/`>` effect on the other side.

### Exactly where this stopped

**`k = 3` is not proved.** What is unfinished, precisely:

* the **composition** is a human step — instantiating `P := a*b` and deriving
  the two bounds on `a*b*s` from shell membership were done on paper, and each
  *step* was machine-checked, but the composition was not encoded;
* the other **twelve leaves** are unencoded (the enumeration says they are
  solution-free at every tested `(a,b)` including `b > a`, so they should be
  k=2-style arguments that do not need `b < a`, but that is a prediction);
* the colour-1 case is already proved for every `k` by route-B; colour 3 is not
  attempted.

What is true that was not this morning: the step the campaign recorded as the
blocker discharges in 1 ms once stated abstractly, and the remaining obstacle
has a two-line reproduction (`P>=1, P*s >= P+1 |= s >= 2`).

---

## Top three roadmap items

**1. Normalise integer bound atoms and retry the other strictness.**
`x >= k <-> x > k-1` over `Sort::Int` is denotation-preserving and it is the
difference between `unknown` at 20 s and 0 ms on both bounding steps of the
`k = 3` leaf. Measured twice, on both sides of the inequality. Cheapest
value-per-line item I found, and it is also B5's smallest reproduction.

**2. A product-abstraction weakening pass.** Replace a maximal repeated
nonlinear monomial by a fresh symbol carrying only its sign/magnitude
consequences, accept `unsat` (sound: a weaker hypothesis set refuting is a
stronger result), decline otherwise. Measured payoff: `unknown` at 20 s to
1 ms on the `k = 3` step. Together with item 1 that step is closed. This is the
mechanical form of the `P := a*b` move I did by hand.

**3. Replace the minimiser's cardinality enumeration with admissibility-guided
deletion.** Mine, flagged against myself. `max_subset_size = 4` matches the
route-B lemmas but the `k = 3` chain needs 5-7, and `C(24, <=4)` already blows
the probe cap. K1 hands over the replacement: greedily delete the hypothesis
whose removal most reduces `normalized_cross_product_count`, probing at every
step — `O(n^2)` syntactic evaluations, `O(n)` solver probes, no cardinality cap.
Bounded, and it is the difference between working at 14 hypotheses and working
at 24.

Runner-up, and the reason item 1 is not item 0 for someone else:
`MAX_CROSS_PRODUCTS = 2` should be a `SolverConfig` budget rather than a literal
(`nra.rs:107`), and **every route that runs should record its decline** —
`int-real-relax` declines silently (`auto.rs:3865` records only on success) and
that cost me a measurement round on the wrong hypothesis.
