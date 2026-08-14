# agent-k — automatic hypothesis minimisation / lemma splitting

Append-only. Dead ends included.

---

## 2026-08-14 — orientation, and a citation correction before any measurement

Read `README.md` (rules 1-10), `CLAUDE.md`, `NEXT-MATH-STACK.md` item 4,
agent-i's `RESULT.md`.

**First finding, and it is a citation defect in my own brief.** The brief says
the measurement is "the 2026-08-12 findings register, item **B4**". It is not.
`docs/plan/findings-register-2026-08-12.md:35` is

> | B4 | `climb.py` hard-coded `k = 4` | Rejected a valid 5-colour seed ... |

The monolithic/decomposed measurement is **`docs/plan/next-actions-from-the-rado-paper-2026-08-12.md:222-234`**,
whose section is *also* numbered "B4" — a different B-list in a different file.
Two documents, two B4s, and the roadmap item cites the register. Recorded in
FEEDBACK.md; anyone chasing the provenance from the roadmap lands on a Python
colour-range bug.

**Second: the primary evidence for the 8-of-8 claim.** Traced to
`docs/plan/proof-approaches-2026-08-12/route-b/REPORT.md:98` and the notebook
`route-b/LOG.md:448-560`. The `.out` files and the `route-b/*.rs` binaries that
produced them are **not in the repository** — `docs/plan/proof-approaches-2026-08-12/route-b/`
contains exactly `LOG.md` and `REPORT.md`. So the seed corpus cannot be re-run;
it has to be re-encoded from the notebook's transcript, which does record every
lemma statement verbatim.

Counting what the notebook actually shows, rather than repeating the headline:

| run | notebook line | matched | mismatched | all unknown? |
|---|---|---:|---:|---|
| `b3_k2` monolithic | 456 | 3 | **9** | yes (4 Incomplete, 5 Timeout) |
| `b3_k2_chain` full hyps | 496 | 4 | **8** | yes |
| `b3_k2_min` minimal | 542 | 11 | 2 | L3, L6 timeout at 60 s |
| `b3_k2_micro` micro | 581 | **16** | **0** | 57 ms total |

So "8 of 8" is the *chain* run, and the monolithic run is **9** mismatches, not
8. The headline number in `REPORT.md:98` ("All 8 attempts") and the table at
`REPORT.md:15` ("3 / 9") disagree with each other in the same file. Neither is
wrong about the phenomenon; the count is.

**Third: `unsat_core` already exists and is structurally unable to do this job.**
`crates/axeyum-solver/src/auto.rs:658-695` is deletion-based minimisation. Line
664:

```rust
if !matches!(solve(arena, assertions, config)?, CheckResult::Unsat) {
    return Ok(None);
}
```

It returns `None` unless the **full** set is already solver-unsat. The B4 case is
precisely the one where the full set is `unknown`. Deletion-based minimisation is
guided by a monotone predicate; the solver's `unsat` is *logically* monotone but
*operationally* is not, so greedy deletion never takes its first step here. The
minimiser has to grow from below, not shrink from above. That is the design
consequence of the measurement and I am recording it before I write any code.

---

## 2026-08-14 — K1. The boundary is not count, and the cause has a constant

Built `~/.cache/axeyum-agent-k/k1` (detached workspace, own `git archive HEAD`
snapshot per rule 7, built on disk). Re-encoded every route-B lemma from the
notebook transcript. Logs in `logs/`.

### Replication at HEAD (`logs/k1-replicate-10s.log`, 10 s budget)

| lemma | 2026-08-12 | today |
|---|---|---|
| M5, M6, M7, ASM | 0.00 s unsat | unsat, 0.000-0.001 s |
| **M8** (opaque `M`) | unknown, 45 s | **unknown, 10 s** — B5 stands |
| L1, L2, L4, L5 | 0.00 s unsat | unsat, 0.000-0.001 s |
| **L3** | **unknown, 60 s timeout** | **unsat, 0.000 s** via `int-real-relax` |
| **L6** | unknown, 60 s timeout | **unknown, 10 s** |
| MONO colour-1 (14 hyps) | unknown | **unknown** |
| CHAIN L3 with full H | unknown | **unknown** |
| CHAIN L5 with full H | unknown | **unknown** |
| CHAIN T1, CHAIN TAIL with full H | unknown | **unsat**, 0.013-0.014 s |

So agent-i is right that `L3` in minimal form is decided today — and the reason
is now measured, below. Two of five full-`H` chain goals *do* close, so "any
monolithic query fails" is too strong; it is 3 of 5 in my re-encoding.

**The vacuity probe I added is the uncomfortable one.** `H` alone returns
`unknown` at 10 s, and `H` minus `t=a*w` — which I expected to be `sat` — also
returns `unknown`. So on this material the solver **cannot tell me whether the
hypothesis set is consistent**. That is exactly the defect the route-B agent hit
at LOG.md:509 (`cT1`/`cT2` were unsatisfiable by construction and could never
fire). Any minimiser must therefore treat "the hypotheses are consistent" as a
THIRD value it usually does not know, not as a precondition it can assert.

### Count is not the variable (`logs/k1-synth-curves.log`)

`L2` (3 hypotheses, closes in 0.000 s) padded with `n` logically irrelevant
hypotheses, budget 5 s, `n` up to 40:

| padding | n=0 | n=10 | n=20 | n=40 | boundary |
|---|---|---|---|---|---|
| disjoint linear | 0.001 s | 0.001 | 0.001 | 0.002 | **none** |
| disjoint degree 2 | 0.001 | 0.003 | 0.018 | 0.073 | **none** |
| disjoint degree 3 | 0.001 | 0.032 | 0.117 | 0.212 | **none** |
| coupled degree 2 | 0.001 | 0.044 | 0.136 | 0.263 | **none** |

**Forty irrelevant hypotheses of degree 3 cost 0.2 s and nothing breaks.** The
count axis is a slope, not a cliff. Whatever B4 saw, it was not hypothesis count.

### It is a single hypothesis (`logs/k1-leave-one-in-L3.log`)

`L3`'s minimal set `{a>=2, b>=1, t=a*w, w>=1}` plus **exactly one** other member
of `H`, 10 s budget:

| added | verdict |
|---|---|
| (none) | unsat 0.001 s |
| `x>=1`, `y>=1`, `t>=1`, `z=a*t`, `x=a*px`, `y=a*py` | **unsat 0.001 s** (6 of 10) |
| `bezout` (`a*u+b*v=1`), `x<=a*b`, `y<=a*b`, `x-y=b*t` | **unknown, 10 s** (4 of 10) |

n = 0 -> 1 is the whole boundary. Adding the *right single hypothesis* is worth
more than adding forty of the wrong ones.

### The mechanism, in the solver's own words (`logs/k1-real-probe.log`)

I first inferred from the route traces that `int-real-relax` "was not reached",
because it appears in the deciding traces and not in the failing ones. **That
inference was wrong and reading the source killed it**: `auto.rs:3865` only
records `int-real-relax` on success, so a decline is invisible in the trace. It
runs every time.

So I posed the same constraints over `Real` sorts, where the NRA engine gets the
whole clock instead of `int-real-relax`'s **one-sixth share**
(`auto.rs:3778 int_real_relax_budget`, `INT_REAL_RELAX_BUDGET_SHARE`):

```
L3 core over Real            -> Unsat 0.002s  nra-real-root
L3 core + bezout over Real   -> Unknown, 0.040s, AT EVERY BUDGET 1s..300s:
  "nonlinear abstraction: 4 cross-products exceed the deterministic
   admission bound of 2 (the multi-variable nonlinear case can OOM the
   relaxation; this needs a nlsat/CAD engine)"
```

`crates/axeyum-solver/src/nra.rs:107` — `const MAX_CROSS_PRODUCTS: usize = 2;`
and the check at `nra.rs:334`. It fires in **40 ms and is completely
budget-independent**: 300 s buys exactly the same answer as 1 s.

**This answers K1's second question definitively: SHAPE, not budget.** The
register's phrasing "minimal hypotheses beat a bigger budget" is correct, and
the reason is a deterministic structural admission cap of **2** distinct
normalized cross-product monomials, not a search that ran out of time.

Corroboration at scale is running on s4/s5/s7 (`ladder-{L3,MONO,L5}.log`): the
full-`H` versions of `L3`, `L5` and the monolithic query are `unknown` at
1 s / 10 s / 60 s / **300 s** so far, with 1800 s and 7200 s rungs still going.

### The killer predicate (`logs/k1-monomial-probe.log`)

Discriminating experiment — `L3` core plus one synthetic hypothesis:

| added | verdict | reading |
|---|---|---|
| `q <= a*b` (fresh q, goal monomial) | **unknown** | +1 uneliminable cross-product |
| `q <= a*c`, `q <= a*t`, `q <= b*t` | **unknown** | same, monomial identity irrelevant |
| `a*u + b*v = 1` (goal vars) | **unknown** | +2 cross-products |
| `q = a*b` (fresh q) | unsat 0.001 s | a *definition* of a once-occurring var |
| `c*d = e`, `c*d + e*f = 1` (all fresh) | unsat 0.000 s | disconnected from the goal |
| `q <= c*d`, `c*d >= 0` (all fresh) | unsat 0.000 s | disconnected |
| `a*b >= 1` (goal monomial vs constant) | unsat 0.001 s | adds no new monomial |
| `a*u = 1` | unsat 0.000 s | `cas-int-units` takes it |

So the property that decides admission is **the number of distinct normalized
cross-product monomials in the goal's connected component, after definitional
elimination** — measured, not assumed, by
`nra_real_root::normalized_cross_product_count` (`nra_real_root.rs:6017`,
`pub(crate)`), which is the same counter `nra.rs:334` gates on.

**That is the minimiser's search heuristic, handed to me by the measurement:**
order candidate subsets by the cross-product count they induce, ascending. It is
a pure syntactic function, costs no solver call, and predicts the cliff.

---

## 2026-08-14 — K2. The minimiser, and what its guards actually test

`crates/axeyum-solver/src/hypothesis_min.rs`, landed in `19f4c769b`.

Design follows K1 rather than the obvious baselines. Greedy deletion is dead on
arrival — it needs the full set to be solver-`unsat` to take its first step, and
the full set is `unknown` by hypothesis. So the search **grows from below**:
subsets of ascending cardinality, ordered by the cross-product count the subset
induces, with a small per-probe budget (250 ms — justified by the measurement
that a sufficient subset closes in 1-2 ms and an insufficient one burns the
whole clock). Once something closes, deletion-based shrink is valid *from that
point*, and it runs.

### A/B on the route-B colour-1 set (`logs/k2-ab.log`)

| goal | monolithic (10 s) | minimised |
|---|---|---|
| `b*t >= a*b` (L3) | **unknown** | **CLOSED** `{a>=2, b>=1, t=a*w, w>=1}` 2.5 s, 541 probes |
| `b*t = a*(px-py)` (L5) | **unknown** | **CLOSED** `{x-y=b*t, x=a*px, y=a*py}` 2.1 s, 446 probes |
| `w >= 1` (T1) | unsat 0.010 s | CLOSED `{w>=1}` 18 probes |
| `x-y <= a*b-1` (TAIL) | unsat 0.012 s | CLOSED `{x<=ab, y>=1}` 66 probes |
| `false` (the whole case) | unknown | **NOT FOUND**, 1471 probes |
| `a*b >= 1` (M5) | unsat 0.010 s | CLOSED `{a>=2, b>=1}` 20 probes |

Both closed subsets are **exactly** the ones the route-B agent found by hand.
The two-and-a-half seconds replace "four attempts and roughly 32 minutes".

The `NOT FOUND` row is the scope boundary and I am not going to dress it up:
the monolithic colour-1 case needs a **chain** — intermediate lemmas nobody
wrote down — not a subset of what is there. Hypothesis minimisation is one half
of B4's problem; the other half is inventing `M1'`..`M7`, and that is proof
search.

### The mutation matrix (`logs/mutation-matrix.log`)

Ran agent-i's strong form: delete one guard at a time, record which tests
notice. First round, nine tests:

| guard | tests killed |
|---|---|
| G-A vacuity | 2 |
| **G-B re-verification** | **0 — DUD** |
| G-C probe strictness | 8 |
| G-D shrink strictness | 8 |
| G-E goal pin (search) | 6 |
| G-F goal pin (verify) | 6 |
| **G-G goal pin (shrink)** | **0 — DUD** |
| G-H cross-product ordering (a NON-guard, harness control) | 0, correctly |

So the guard I would have described as the most important one — "the reported
subset is independently re-verified" — was **deletable with every test green**.
Every other test's subset re-verifies trivially, so nothing exercised it. Added
`re_verification_is_respected` (probe at 5 s, verify at 1 ns, expect
`NotFound`); it now kills G-B and only G-B.

`G-G` stays a measured dud and I am recording it as **conservative, not
load-bearing** rather than shipping a control that cannot fire. The reasoning is
that whenever the un-pinned shrink would differ, the surviving subset is
inconsistent, which `G-A` refuses — and I measured that rather than asserting
it: the paired deletion `G-A + G-G` kills exactly the same two tests as `G-A`
alone. No forgery of `G-G`'s shape exists while `G-A` is present.

### The deliberate wrong answer, exhibited

`an_unentailed_goal_is_not_found_not_closed` survived every *single* deletion.
It is not a dud — it is guarded in depth. Deleting `G-B` **and** `G-C` together:

```
an unentailed goal was reported closed:
  Closed { indices: [], consistency: Consistent, probes: 2 }
```

for the goal `a*b >= 3` under `{a >= 2, b >= 1}` — an **empty** hypothesis set,
i.e. the claim that `a*b >= 3` is a tautology. It is false at `a = 2, b = 1`.
That is the wrong-answer generator constructed deliberately, and two named
guards stand between it and a verdict.

Gates on the live worktree: `cargo test -p axeyum-solver --lib --features full`
**1138 passed** (1128 at HEAD + 10). `scripts/check-fmt-complete.sh` 883 files —
and I mutation-tested the *gate*: appending an unformatted line made it report
`1 file(s) not formatted: crates/axeyum-solver/src/hypothesis_min.rs`, so it
really does examine the new file. `clippy --all-targets --features full` clean.

---

## 2026-08-14 — K3. The k=3 leaf: a new structural fact, and where it stops

### First, an enumeration nobody had run (`logs/k3-ground-truth.log`)

`k3_ground_truth.py` re-derives the shell colouring from
`PROOF-BRIEF.md:20-38` and enumerates every monochromatic solution for
`2 <= a <= 7`, `b <= 9`, `gcd(a,b) = 1`, `N <= 3000`. Two results:

1. `b < a`: **solution-free in 17 of 17** pairs (reproduces the campaign's
   21/21 on a smaller range).
2. **Every defect, in every defective pair, sits in ONE leaf**: colour 2, with
   `x` in the right shell, `y` in the left shell, and `v(z) = 2`. Colour 1 and
   colour 3 have **no** solutions at any tested `(a,b)`, on either side of
   `b = a`.

That is new and it shrinks the k=3 case analysis a lot: the route-B notebook
budgeted "roughly 10 leaf cases"; only **one** of them can possibly need `b < a`.
My leaf count (1 + 9 + 4) matches the notebook's own estimate exactly, which is
the cross-check that the reconstruction is faithful.

### The brief's stated blocker is not a blocker

`REPORT.md:86-88` says cases 2 and 3 need "degree-3/4 inequalities in three
variables". The critical leaf's closing inequality is exactly that:

```
a>=2, 1<=b<=a-1, a^3+a^2 <= a^2*b + 2*a*b  |=  false     unsat, 0.002 s
CONTROL  a>=2, b=a+1, same inequality                     sat,   0.001 s
```

Two milliseconds, with the control firing on precisely the `b = a+1` defect
family. The degree and the variable count are not the obstacle.

### Where it does stop (`logs/k3-leaf.log`, `logs/k4-rounding.log`)

The leaf's chain forces `s = a+1` from two bounds. Both bounding steps stall,
and minimisation cannot help because the *minimal* form already fails:

```
a>=2, b>=1, a*b*s >= a^2*b + 1  |=  s >= a+1      unknown, 20 s   (3 hypotheses)
CONTROL: drop the +1                              sat,     0.002 s
```

Posing the 24-hypothesis leaf and letting the minimiser at it hits the probe cap
on every chain goal (`NOT FOUND`, 4000 probes) — but that is a red herring, and
the hand-derived minimal set proves it: three hypotheses, still `unknown`.

**K4 localises it to two independent effects, each of which I measured
separately.**

| query | verdict |
|---|---|
| `s > a  \|= s >= a+1` (pure LIA rounding) | unsat 0.000 s |
| `P>=1, P*s >= P+1 \|= s > 1` (real-valid half) | unsat 0.000 s |
| `P>=1, P*s >= P+1 \|= s >= 2` (the two composed) | **unknown 1.5 s** |
| `P=6, P*s >= P+1 \|= s >= 2` (instantiated) | unsat 0.000 s |

Each half is microseconds and the composition is `unknown`. And `s >= 2` and
`s > 1` are the **same statement over the integers** — the verdict depends on
which side of the inequality the constant is written on. That is B5's
"generalising made it harder" in its smallest possible form and it is a defect,
not a hardness result.

Second effect: the product `a*b`. `P>=2, a>=2, P*s >= a*P+1 |= s > a` is
**unsat in 0.001 s** with `P` a free variable; add the definition `Q = a*b` and
the identical query is **unknown at 20 s**.

### So the k=3 critical leaf's arithmetic core does discharge — in pieces

Abstract `P := a*b` (sound: the conclusion needs only `P >= 2`) and every step
lands, each with a control where a control is meaningful:

| step | verdict |
|---|---|
| A `a>=2, b>=1 \|= a*b >= 2` | unsat 0.000 s |
| B `a*(a*b) = a^2*b` | unsat 0.000 s |
| C `P>=2, a>=2, P*s >= a*P+1 \|= s > a` | unsat 0.001 s (control: **sat**) |
| D `s > a \|= s >= a+1` | unsat 0.000 s |
| E1 `P>=2, P*s <= a*P+2*P-1 \|= s < a+2` | unsat 0.001 s (control: **sat**) |
| E2 `s < a+2 \|= s <= a+1` | unsat 0.000 s |
| F `a>=2, 1<=b<=a-1, s=a+1, z=a^2*s, z<=a^2*b+2*a*b \|= false` | unsat 0.002 s (control at `b=a+1`: **sat**) |

Note `CHAIN E` *unsplit* (`|= s <= a+1`) is unknown at 20 s while `E1 + E2` are
1 ms — the same `>=`/`>` effect, on the other side.

**What I am NOT claiming.** The composition is a human step: instantiating
`P := a*b`, and deriving the two bounds on `a*b*s` from the shell membership,
were done on paper and each *step* was machine-checked. I did not encode the
composition, I did not do the other twelve leaves, and I did not run the
colour-1 or colour-3 cases (the enumeration says they are solution-free at every
tested `(a,b)`, so they should be the k=2-style arguments). **k = 3 is not
proved.** What is now true that was not this morning is that the step the
campaign recorded as the blocker discharges in 1 ms once it is stated
abstractly, and the remaining obstacle has a name and a two-line reproduction.

---

## 2026-08-14 — a rule-9 mistake of my own, disclosed

Committing the PLAN.md row swept the Lean lane's **uncommitted** PLAN.md edit
(`ADR-0438 -> ADR-0439` on the "Immediate action" line) into my commit
`20e1f9805`. Pathspec discipline stops you sweeping files you did not touch; it
does nothing when the file you legitimately touch already carries someone else's
uncommitted work, which is exactly what rule 9 warns about and I still walked
into it.

Nothing was reverted and nothing was lost — the text that landed is the Lean
lane's own, forward-moving. Only the attribution is wrong. I disclosed it in the
amended commit message rather than doing history surgery underneath a codex
session that commits every few minutes.

The generalisable fix, for the next lane: **`git diff PLAN.md` before staging
it**, and if the diff contains anything you did not write, stage with
`git add -p` and take only your own hunk. `git add PLAN.md` is not safe on this
file no matter how careful the pathspec on `git commit` is.

**Second, smaller footgun in the same area.** `Agent: agent-k` followed by a
blank line and then `Co-Authored-By:` is **not** parsed as a git trailer — git
only reads the last paragraph, so `git log --format='%(trailers:key=Agent)'`
prints nothing. `git log --grep='Agent: agent-k'` still finds both commits, so
rule 10's intent holds, but anyone building tooling on `%(trailers:)` will see
an empty lane on every commit in this campaign that used that layout. Put
`Agent:` in the SAME paragraph as `Co-Authored-By:`.

---

## 2026-08-14 — closing state

Landed: `19f4c769b` (the minimiser), `20e1f9805` (PLAN.md row).
Deliverables here: `RESULT.md`, `FEEDBACK.md` (9 items, cited by file and line),
`logs/` (10 measurement logs), `artifacts/` (the four measurement harnesses,
`mutate.py`, `k3_ground_truth.py`).

Still running when I stopped: the 7200 s rung of the budget ladders on s4
(`L3`), s5 (`MONO`) and s7 (`L5`). All three are `unknown` through the 1800 s
rung. If the 7200 s rung ever returns `unsat` the shape conclusion is wrong and
`RESULT.md` must be corrected — but the `MAX_CROSS_PRODUCTS` guard is a
deterministic 40 ms check, so I do not expect it and would want to know why.

Not done, and named rather than buried: the `k = 3` composition, the other
twelve leaves, and the admissibility-guided search that would let the minimiser
work at 24 hypotheses instead of 14 (FEEDBACK F9, RESULT roadmap item 3).
