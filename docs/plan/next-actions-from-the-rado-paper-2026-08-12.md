# Next actions, from the Rado paper — 2026-08-12

What to do next, split into work **for** the paper and work **because of** what
the paper exposed about axeyum. Every claim below was measured in this
session; where a number appears, the command that produced it is in the lab
notebooks under
[`proof-approaches-2026-08-12/`](proof-approaches-2026-08-12/README.md) or in
`docs/plan/cas-smt-capability-2026-08-12/`.

Two things changed today that reorder everything downstream:

- The general-`k` shell bound is **proved** (Theorems 1–3 in
  `../axeyum-rado-paper/latex/sections/03_shell.tex`), where this morning it
  was *verified at 11 points and asserted in a Python script*. Lower bounds on
  the `b = a-1` line now follow from a theorem, not a search.
- `axeyum-cas` acquired its first dependent. The solver can now refute
  polynomial identities and integer-units goals with a re-checkable
  certificate (ADR-0386).

---

## Track A — for the paper

Executed in `../axeyum-rado-paper`. Ordered by value.

### A1. Fill the `k = 4` row: `R_4(5(x-y)=4z) = 741`, `R_4(6(x-y)=5z) = 1501`

**Highest-value item in either track.** It takes the paper from two exact
values to four, which is the difference between a note and a paper.

Both lower bounds are now *free*: Theorem 1 applies at `(a,b,k) = (5,4,4)` and
`(6,5,4)` — `b < a`, `gcd = 1`, `k >= 2` — giving `N = 740` and `N = 1500`
with no computation. Verified by hand this session. Each value therefore needs
**one refutation** and nothing else.

The refutation side is already scoped by the other machine's campaign on 741:
746 of 4096 cells refute instantly by propagation, 1,132 exhaust 200k
conflicts at ~4–9 s each, and 2,210 are untouched. The conclusion recorded
there is that the hard subtree needs **adaptive deeper splitting**, not more
hardware. That is the concrete next engineering step.

### A2. Check the Lean export with real Lean

The paper states the export has not been validated by real Lean, and that is
accurate: `lean`, `lake` and `elan` are all absent on the machine that
produced it (verified). The module is 42 KB, self-contained, with **0 `sorry`
and 0 `axiom`** (verified by inspection), ending in `#print axioms`.

One command on any host with a toolchain converts *"we emitted a Lean module"*
into *"an independent kernel accepted it."* Very high credibility per unit of
effort, and it is the single cheapest item on this list.

### A3. Promote the `k = 5` non-tightness to a proposition

Currently stated as an observation. The material for a proposition exists:

- the shell construction gives 318 at `(a,b,k) = (3,2,5)`;
- a solution-free 5-colouring of `[350]` is verified (re-verified this session
  by an independent enumerator: 0 monochromatic solutions);
- exhaustive enumeration over **644,956 cut vectors** shows 318 is the ceiling
  of the entire two-sided shell *shape*, not merely of the canonical widths.

So the gap is a failure of the shape, and no parameter tuning can close it.
That is a bounded negative result and deserves to be stated as one.

### A4. Chase a better construction at `k >= 5`

The genuine open mathematics here, and the most likely source of a second
result. Two leads, both measured:

- the verified 350-witness is **one point** away from clean structure — the
  only `j` where `(v_3(j) = 1)` and `(colour = 2)` disagree is `j = 60`;
- it shows real 3-adic periodicity: `col[j] = col[j+p]` agrees **63 %** at
  `p = 18` against a 20 % chance rate, with `p = 9, 27` (powers of `a`) and
  `p = 78, 156` (the shell cuts) close behind.

A strictly periodic unit colouring was probed and did **not** pay off (the
search did not converge; recorded as a dead end). A perturbed-valuation family
is the untried direction.

### A5. Referee pass on Theorem 3 (Rigidity)

It is the newest and least-reviewed of the three, and its `a = 2` corner was
found only at the end — by an agent, and it was absent from *both* prior
sweeps (on the line `b = a-1`, `a = 2` means `(2,1,k)`, which neither
enumeration contained). A theorem whose last corner surfaced that late
probably has another.

Specific target: the width-lemma obstruction occurs 117 times, every one at
`a = 2, M = N+1`, and is closed by a defect induction. That induction is the
part to re-derive independently.

### A6. Complete the `k = 3` unbounded refutation

The `forall`-route proved `k = 2` for symbolic `a` **and** `b` over unbounded
`Z` without assuming `b < a`, and got **1 of 3 cases** at `k = 3`. Cases 2 and
3 need `b < a` and degree-3/4 inequalities in three variables — the shape that
defeated every monolithic attempt. See Track B (B4, B6): this may be easier
*after* the tooling work than before it.

### A7. Citation and novelty sweep before submission

Two references are marked NOT READ in `latex/bib/references.bib`; the Li SSRN
item is a paywalled, non-peer-reviewed preprint cited only for position.

Notation and citations against Chang–De Loera–Wesley were verified this
session **against the rendered PDF, not the source tarball** — the tarball on
arXiv is an earlier version missing three tables, and counting it suggested a
citation error that does not exist. Confirmed correct: their four-colour table
*is* Table 10; Lemma 4.1 *is* `R_k >= a^k` for all `k` and all `b`; Lemma 4.2
*is* the `b = a-1` bound stated for `k = 3` only.

### A8. The two open editorial calls

- **10 pt vs 11 pt.** The paper is 12 pages at 10 pt (amsart's own default and
  AMS house size) and ~14 at 11 pt. One-line revert either way.
- **Whether the CAS verification earns an appendix line.** 166 exact symbolic
  checks in `a` and `b`, 19 of them negative controls that must and do refuse
  to vanish. It is currently absent from the prose because the agent that
  wrote the appendix could not run it.

---

## Track B — because of the paper

Executed in this repository. Ordered by value.

### B1. Gate the narrative, not just the numbers

**Two paper claims drifted this session, and a gate caught neither.**

1. `R_5(3(x-y)=2z) > 319` appeared in the abstract while the ledger held a
   **checked** witness for 350 — understating a verified result by 31. The
   macro's own comment named the ledger as its source of truth.
2. The Method section justified cube-and-conquer with an out-of-memory kill
   that ADR-0381 had already diagnosed and repaired (the core was buffering
   the whole DRAT proof in RAM). Nobody re-measured after the fix, so the
   claim was not merely stale but **unsupported**.

`check_claims_complete.py` gates *exact values* and did its job on both. It
has no purchase on narrative claims about performance, feasibility, or
frontier bounds. Both drifts were caught by a human reading prose.

**Action:** extend the gate to frontier bounds (compare against the ledger's
retained best), and require performance claims to carry the commit they were
measured at.

### B2. `axeyum-search` has never compiled

Discovered while building the colouring encoder. The crate:

- is **absent from the workspace `members` list**, so `cargo build -p
  axeyum-search` fails outright and nothing builds or tests it;
- declares `pub mod certify;` and `pub mod search;` for files that do not
  exist;
- claims in `colouring.rs:10` that "`tests/encoding_parity.rs` compares them
  directly" while `crates/axeyum-search/tests/` is an **empty directory** —
  the differential gate it advertises was never written.

It now also duplicates `ColouringProblem`, which landed properly in
`axeyum-cnf::colouring`. A crate that has never compiled is worse than an
absent one: it advertises a guarantee it does not provide.

**Action:** fix or delete. If resumed, collapse
`axeyum-search/src/colouring.rs` onto `axeyum_cnf::colouring`.

### B3. The frontier ratchet is machine-dependent

`frontier_bv_reduction` fails on this 4-core box at 26 against a committed
baseline of 30, with the lost instances (N = 27–30) returning `unknown` at
~4009 ms against a **4000 ms budget** — at the measurement's resolution limit.

Bisected this session across three commits (the CAS bridge, the merge, and the
pre-merge lane head): **identical failure at all three**, including with the
solver untouched. Independently confirmed by the bridge agent, which
recompiled with its hook disabled (`if false && …`) and saw the same failure.
Nothing in this session caused it.

A wall-clock ratchet that cannot be reproduced on a developer box will keep
crying wolf and will train people to ignore a genuine regression.

**Action:** declare a reference machine, or normalize the budget against a
calibration measurement taken at run time. Until then, **never commit a
lowered frontier value measured on a small box** — it ratchets the roadmap
floor down on a slow reading.

### B4. Manual lemma-splitting is a tool gap, not a technique

Measured: **every** monolithic query carrying a full hypothesis set returned
`unknown` (8 of 8 attempts), while the same content split into 3–4-hypothesis
lemmas closed in 0.00 s. Minimal hypotheses beat a bigger budget.

That decomposition was human work — four attempts and roughly 32 minutes of
solver time went into finding a decomposition the tool would accept. An
automatic hypothesis-minimization or lemma-splitting layer is a real feature,
and it is the difference between a tool an expert can coax and a tool that
works.

### B5. "Generalising made it harder" is backwards

Measured: a lemma with an opaque symbol `M` timed out at 45 s; the identical
fact at `M := a^2` was `unsat` in 0.01 s.

Symbolic structure should *help*. This is the diagnostic signature of a
representation problem, not a hardness result, and it should be treated as a
defect rather than a quirk.

### B6. Finish the CAS bridge

Landed (ADR-0386): `cas-identity-refuter` and `cas-int-units`, with a trusted
checker that imports nothing from `axeyum-cas` and re-expands using a
different algorithm. Measured: `a >= 2 ∧ a·p = 1` went from a **15.00 s
timeout** to **79 µs**.

**Honest scope note, from the implementing agent's own A/B:** standalone
polynomial-identity disequalities were *already* decided in 1–5 ms by
`int-real-relax` / `nra-real-root`. The identity route's real contribution is
identities sitting beside something the real relaxation refuses (underspecified
`div`, rational division), plus a re-checkable certificate where the relaxation
gives none. The **units/divisibility route is where the unambiguous new
capability is.**

Remaining, in order:

- `cas-int-units` declines on `(a+1)·p = 1` — it requires a single monomial
  after normalization, so **factorization** is the next step (recorded as the
  revisit trigger in ADR-0386);
- **Gröbner ideal membership** for the nonlinear-equality fragment
  `nia-linearize` currently declines — `groebner_basis` and `ideal_contains`
  already exist and are unused;
- **`gosper_sum` for closed forms** — this session proved the same geometric
  sum `(a-1)Σ_m = a^(m+1) - a` three separate ways (by hand, by `MvPoly` at
  ten values of `m`, and by Lean induction). One symbolic call should do it.

### B7. Lean kernel: divisibility and valuations

`nat_prelude` landed with **zero axioms** (ADR-0385) — `add`/`mul`/`pow`, the
algebraic laws, `Nat.le`, and the `Eq` combinators, all proved because `Nat`
is a real inductive with a real recursor. ADR-0389 has since added the proved
`Nat.dvd`, `dvd_mul`, and `dvd_add` foundation without changing that boundary.

`Nat.le` ships narrowly and is documented as such: no `lt`, antisymmetry,
totality, decidability, or `le_of_succ_le_succ` inversion.

**The remaining divisibility and valuation library is the gating item** for formalizing anything
genuinely number-theoretic — which is to say, for formalizing this paper's
actual theorems rather than its arithmetic identities. Route: inversion of
`<=`, subtraction, then gcd by well-founded recursion (`Acc`-shaped recursion
is no longer an unprobed kernel shape: reflexive and recursive-indexed fields
now admit. The remaining work is to declare `Acc`/`WellFounded`, verify the
generated `Acc.rec` is usable, and check one end-to-end gcd definition; native
well-founded source elaboration remains a separate frontend capability).

### B8. Regenerate the 34 binary-DRAT proofs

34 evidence rows are `replay-only` because they are binary DRAT — a dialect
axeyum's own `parse_drat` cannot read. They were only ever checked by the
external drat-trim.

Regenerating them with axeyum's own proof core (which emits text DRAT) and
verifying with `check_drat_backward` lifts them to `checked` and **finally
removes the external checker from the trusted path** — which is the identity
claim in ADR-0002. Minutes of compute; the largest instance solved in ~130 s.

### B9. Re-examine the search/certification strategy

Backward checking (66×, ADR-0382) and streaming emission (ADR-0381) changed
the cost model that cube-and-conquer was designed around. The decomposition
may now be over-engineered for some instances.

Measured ladder this session, axeyum's own CDCL with streaming DRAT,
monolithic (no decomposition):

| instance | clauses | verdict | wall |
|---|---|---|---|
| `F_56` | 5,206 | UNSAT | 0.0 s |
| `F_81` | 8,044 | UNSAT | 0.8 s |
| `F_103` | 10,276 | UNSAT | 7.2 s |
| `F_226` | 35,858 | not finished in 65 min | — |

The scaling is a cliff, not a slope: roughly **9× per 25 % more clauses**.
Note `F_103` is a value Chang–De Loera–Wesley computed with CaDiCaL, reporting
*up to 20 hours* for some of their four-colour upper bounds; ours refutes it
monolithically in 7.2 s.

**Action:** decide the decomposition threshold from this curve rather than
inheriting it.

---

## Cross-cutting lessons

Recorded because all three recurred, and each cost real time.

1. **Passing tests do not discipline causal claims.** Three of the
   orchestrator's own errors this session had the same shape: the data were
   correct and the inference was wrong — a base case using `min` for `max`; a
   counterexample family verified at `k=3` and generalized without checking
   `k>=4`, where it is false; and a rigidity phenomenon attributed to the
   wrong inequality. The last was refuted by a *discriminating* experiment
   (which proof branch fires?), not by re-checking numbers.

2. **Verify against the rendered artifact, not the source.** Counting tables
   in the arXiv source tarball produced a citation error that does not exist;
   the tarball is an earlier version than the published PDF.

3. **Scope discipline is a recurring cost.** A mathematics paper does not
   discuss memory, hosts, worker counts, or checker benchmarks. The Method
   section was cut from 70 lines to 21 and the verification detail moved to an
   appendix. Systems material expands unless actively resisted.
