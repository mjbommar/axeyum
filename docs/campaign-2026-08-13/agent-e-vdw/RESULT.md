# agent-e — van der Waerden numbers, certified end to end in pure Rust

**Standing table.** Last update 2026-08-13, 23:05 (wind-down). Raw record in
`logs/` and in the lane logs on s5/s6; the ledger entries are in the repository
at `artifacts/claims/vdw/`.

## What counts as a value here

`w(r; k_1,…,k_r)` is the least `N` such that every `r`-colouring of `[1,N]`
contains, for some colour `c`, a monochromatic arithmetic progression of length
`k_c`. `W(r,k)` is the diagonal case. A row is a **value** only when both sides
are discharged:

* `n = N − 1` **sat**, model decoded to a colouring and replayed by
  `VanDerWaerden::first_violation` — a dynamic program over pairs of members of
  the colour class that computes the longest progression and shares no code with
  the encoder — then cross-checked against the encoder's own view, then replayed
  a third time in Python by `scripts/check-claim-certificates.py`;
* `n = N` **unsat**, DRAT proof from axeyum's own proof-producing CDCL core,
  re-derived by axeyum's own backward DRAT checker.

No external solver and no external checker appears anywhere: no kissat, no
cryptominisat, no z3, no drat-trim (ADR-0002).

## The headline

**Thirteen van der Waerden numbers certified from both sides by a fully pure
Rust, self-checked pipeline** — encoder, solver, proof producer and proof
checker in one system, one process per value.

Every one **reproduces a published number**. The contribution is the
certification, not the value, and that is a deliberate result rather than a
consolation: a literature audit (§ Novelty) found **no classical van der Waerden
number carrying a machine-checked UNSAT proof in the peer-reviewed record**.

## A. Certified values

| value | N | clauses @N | DRAT steps | proof | solve | check | published by |
|---|---:|---:|---:|---:|---:|---:|---|
| W(2,3) = w(2;3,3) | 9 | 59 | 5 | 33 B | 0.00 s | 0.00 s | Chvátal 1970 |
| W(3,3) | 27 | 668 | 1,641 | 43 kB | 0.01 s | 0.01 s | Chvátal 1970 |
| W(2,4) | 35 | 479 | 256 | 5 kB | 0.00 s | 0.00 s | Chvátal 1970 |
| **W(2,5)** | **178** | **8,278** | **2,153,837** | **139 MB** | **20.05 s** | **22.19 s** | Stevens–Shantaram 1978 |
| w(2;3,4) | 18 | 153 | 29 | 361 B | 0.00 s | 0.00 s | AKS Table 1 |
| w(2;3,5) | 22 | 204 | 100 | 2 kB | 0.00 s | 0.00 s | AKS Table 1 |
| w(2;3,6) | 32 | 391 | 302 | 8 kB | 0.00 s | 0.00 s | AKS Table 1 |
| w(2;3,7) | 46 | 752 | 937 | 29 kB | 0.01 s | 0.00 s | AKS Table 1 |
| w(2;3,8) | 58 | 1,140 | 4,158 | 168 kB | 0.05 s | 0.03 s | AKS Table 1 |
| w(2;3,9) | 77 | 1,931 | 19,592 | 1.0 MB | 0.10 s | 0.10 s | AKS Table 1 |
| w(2;3,10) | 97 | 2,973 | 164,912 | 10.9 MB | 1.15 s | 1.30 s | AKS Table 1 |
| w(2;3,11) | 114 | 4,014 | 1,017,863 | 83.9 MB | 9.71 s | 11.96 s | AKS Table 1 |
| w(2;3,12) | 135 | 5,521 | 6,347,847 | 623 MB | 82.21 s | 110.28 s | AKS Table 1 |

AKS = Ahmed, Kullmann and Snevily, arXiv:1102.5433 (Discrete Applied
Mathematics 174 (2014) 27–51), Table 1.

All thirteen carry a claim-ledger entry: **13 claims validate with 0 errors and
re-check with 0 errors.** Twelve carry the DRAT proof in-tree and it is
re-checked there; `w(2;3,12)`'s 623 MB proof is recorded as **NOT re-checked in
this tree**, hash-pinned with a regeneration recipe, rather than passed
silently.

`W(2,5) = 178` is the load-bearing one: 2,153,837 proof steps, produced and
re-derived in 43 seconds by one process (§ Novelty for what that compares to).

## B. Not established — stated exactly

Half a value is not a value. Every one of these is recorded by **which side was
discharged and which was not**.

| target | lower side (`n = N−1`) | upper side (`n = N`) | stopped by |
|---|---|---|---|
| **w(2;3,13) = 160** | **sat, replayed** | **not certified** | monolithic proof 6.0 GB, checker OOM-killed on 26 GiB; cover at depth 8 refuted **247 of 256 cells**, each re-derived, then OOM-killed at 7.4 GB of cell proofs. Nine cells short. |
| w(2;3,14) = 186 | not established (CDCL hit its default conflict budget) | not attempted | wound down |
| w(2;3,15) = 218 | not established (same) | not attempted | wound down |
| **W(4,3) = 76** | **not established** | **not attempted** | the *lower* side is the hard one: CDCL exhausted its default budget in 44 s, 14 lanes of `min_conflicts` found nothing in 35 min, randomised backtracking burned 4,000,013,081 nodes in 265 s, and the cover run was OOM-killed |
| W(3,4) = 293 | not attempted | not attempted | wound down |
| W(2,6) = 1132 | not attempted | not attempted | far beyond the proof-size wall |

Nothing above was rounded, inferred or extrapolated. A timeout is recorded as a
timeout, an OOM as an OOM.

## C. `w(2;3,20)` — the census, and a correction to the brief

**The brief's premise is wrong and this is the most important line in this
file.** `w(2;3,20)` was described as open since 2011 with a conjectured lower
bound of 389. In fact:

* **389 is a *certified* lower bound, not a conjecture.** AKS Appendix A.1
  prints an explicit palindromic good partition of `[1,388]`. Their Table 2
  lists it under "conjectured precise lower bounds", where "conjectured" attaches
  to *precision*, not to the bound.
* **The value is very probably already settled.** Wikipedia's raw wikitext
  attributes `w(2;3,20) = 389` to Kouril, *Leveraging FPGA clusters for SAT
  computations* (ParaFPGA15, Advances in Parallel Computing 27, 2015), marked
  "verified". That paper's abstract reports "four new off-diagonal van der
  Waerden numbers" and exactly four Wikipedia rows cite it. **The body is
  paywalled and I did not read it**, so this is inference from the citation
  pattern plus the abstract's count — strong enough that claiming the cell as
  open would be wrong.
* The genuinely open row begins at **`t ≥ 21`** (AKS Table 2: 416, 464, 516, …,
  none closed).
* OEIS **A007783** stops at `a(19) = 349` and has no `b`-file, so if Kouril 2015
  is what it appears to be, that sequence is one term stale.

### The census, as measured

`w(2;3,20)` at `n = 389`: **42,204 clauses over 778 variables**, built in under
10 ms. The instance is tiny; the difficulty is pure search, exactly as the brief
said.

Split by the colours of points 2, 4, 6, 8, 10, 12 into 64 cells, one core, 90 s
per cell, hard 900 s cap:

| | n = 388 | n = 389 |
|---|---:|---:|
| cells refuted (proof produced) | 14 | 14 |
| cells open at 90 s | 9 | 9 |
| cells not reached before the cap | 41 | 41 |

Whole-instance attempts: CDCL on `n = 388` returned `unknown` at a 300 s
deadline; randomised backtracking on `n = 388` was killed at wind-down with no
witness. **No side of `w(2;3,20)` is established here.**

Two things the census does say. The refuted/open split is **identical at 388 and
389**, so at this depth the cells that close are insensitive to the boundary —
depth 6 is nowhere near enough to separate them. And 14 cells closing in
milliseconds beside 9 that survive 90 s is the same hard-corner shape the
`w(2;3,13)` cover showed: the survivors are the cells whose branch points take
the long-progression colour.

For scale: Ahmed–Kullmann–Snevily needed **~196 CPU-years on 200 processors**
with a purpose-built solver for `w(2;3,19) = 349`, and Kouril used a cluster of
over 200 FPGAs. This lane's contribution to the cell is the census and the
correction, nothing more.

## D. Novelty — what is actually new here

The values are not new. The audit that established that also established what
is:

* **No classical van der Waerden number carries a machine-checked UNSAT proof in
  the peer-reviewed record.** Kouril–Paul (`W(2,6)`), Kouril (`W(3,4)`) and AKS
  (the `w(2;3,t)` row) produced none; AKS write that compressing their
  resolution proofs into an object "which could be verified by certified
  software" *"would be highly desirable"*. Marijn Heule's `vdWaerden` repository
  holds 44 certificates and **every one is a lower-bound colouring**.
* The only machine-checked vdW refutations anywhere are from 2026 and are
  Lean-based: **PBLean** (arXiv:2602.08692) covers `W(2,3) = 9` and the upper
  half of `W(2,4) = 35` via VeriPB; an **unreviewed** repository claims
  `W(2,5) = 178` via 3,627 cubes of cube-and-conquer, per-cube LRAT,
  LRAT-Catcher composition and a Lean 4 reflection pass.
* **No pure-Rust van der Waerden pipeline exists** on GitHub as far as the
  survey reached.

So the defensible claim is: **`W(2,5) = 178` and the `w(2;3,t)` row for
`t = 4..12` are, as far as this audit reached, the first van der Waerden numbers
certified by a single self-checking system with no external solver and no
external proof checker** — ours reaches `W(2,5)` in one process and 43 seconds
where the one prior certification of that value needed a six-tool pipeline.

The claim is bounded by the audit, and the audit is written down: full text of
arXiv:1102.5433, OEIS A007783 and A005346, `gh search` over the vdW repository
space, and the 2026 Lean/VeriPB work. If someone has certified `w(2;3,9)` and I
did not find it, the certification is still real and the priority claim is not.

## E. How each side is checked

| side | produced by | checked by | independent of the producer? |
|---|---|---|---|
| `n = N−1` sat | axeyum CDCL | `VanDerWaerden::first_violation` (longest-progression DP over pairs of class members) | yes — the encoder enumerates (first term, difference) over `[1,n]` and never computes a longest progression |
| | | `ColouringProblem::first_monochromatic` | no — shares the encoder's view; run as a weaker cross-check |
| | | `check-claim-certificates.py`, in Python | yes — third derivation, different language, grows progressions forward from pairs |
| `n = N` unsat | axeyum CDCL, DRAT streamed to disk | `check_drat_backward` | yes |
| | | the ledger checker validates the CNF clause by clause **and its per-colour clause counts** | yes — catches the symmetry trap and any missing progression |

## F. Residual trust

1. **Encoding faithful to the definition** — guarded by 13 published-value
   reproductions from both sides, by `first_violation` being an independent
   derivation, and by the Python re-derivation in the ledger checker.
2. **Symmetry breaking sound** — colour classes are ordered by least element
   only within blocks of equal progression length; the diagonal case keeps the
   whole-palette break because its colours genuinely are interchangeable. Not
   assumed: the committed control
   `whole_palette_symmetry_breaking_produces_a_wrong_unsat` shows the unblocked
   version turning satisfiable `w(2;3,4)` at `n = 17` into `unsat` with a valid
   DRAT refutation. Scans of `w(2;3,5)` over `n ≤ 21` and `w(2;3,6)` over
   `n ≤ 31` — 52 instances — produced **zero** flips, so a control built on
   either would have tested nothing.
3. **No reduction to trust.** Unlike the off-diagonal Schur family there is no
   subsumption pass here: measured ratio 1.000, because every length-`k`
   progression has exactly `k` points and no two nest.
4. **axeyum's CDCL core and backward checker** — proofs are 5 to 2,153,837 steps
   and every one is re-derived, not accepted.

## G. Artifacts

```
artifacts/claims/vdw/vdw-<r>-<k...>/         in the repository: claim.json,
                                             witness_<N-1>.txt, F_<N>.cnf,
                                             F_<N>.drat.gz
~/scratch/agent-e/bundles/<cell>/            full uncompressed bundles
s6:~/scratch/agent-e/out/cover_w_2_3_13/     the 247-of-256 cover, its ledger
                                             and 7.4 GB of cell proofs
s5:~/scratch/agent-e/census_w2320_{388,389}.out   the census
vdw_frontier.rs                              the driver (outside the repo by
                                             the campaign ownership map)
```

Committed to the repository: `crates/axeyum-search/src/vdw.rs`,
`crates/axeyum-search/tests/vdw.rs`, the `vdw` spec in `family.rs`, the family's
semantics in `scripts/check-claim-certificates.py`, and
`artifacts/claims/vdw/SEMANTICS.md`.
