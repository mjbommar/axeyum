# AC-Bridge: additive combinatorics / discrete Fourier analysis on finite
# 2-groups, toward the Lemire endpoint

Date opened: 2026-08-20
Status: ad hoc research project, outside the normal roadmap/gates.
Parent: docs/research/10-cas/adhoc-blocker-sweep-2026-08-20/ (ten-lens sweep)
and docs/research/10-cas/lemire-review-2026-08-20-reaim.md.

## Mission

Develop the missing mathematics for the Lemire endpoint inside additive
combinatorics / discrete Fourier analysis on finite abelian 2-groups — the
field the sweep identified as the easiest to develop genuinely new
mathematics in, because (i) the surviving target has measured exponential
slack, (ii) every candidate lemma is machine-falsifiable in seconds, and
(iii) the identifiable gap ("one grading further" than global
hypercontractivity) is small and well-scoped.

Novel mathematics produced here is a deliverable in its own right, even
where it does not close the endpoint. Detours for breadth are in scope.

## The objects (fixed notation for the whole project)

- `G_ell` = principal units of `F_2[x]/x^(ell+1)`, `|G_ell| = 2^ell`,
  with canonical decomposition `G_ell ~ prod_(i odd, i<=ell) Z/2^(k_i)`,
  `k_i = min{ m : i*2^m > ell }` (the Witt / Efron--Stein grading).
- `D_e` = endpoint class discrepancies of the degree-`n` Mangoldt
  populations, `n in {2ell+1, 2ell+2}`; `S_chi` = Hayes character sums;
  `M_2 = sum |S_chi|^2`; `M_4` = the product-constrained fourth moment;
  `K_4 = M_4 - (Wick pairings)` the connected cumulant.
- Cylinder data `B_j(b)`, conductor filtration, and the exact-conductor
  layers as already computed by the axeyum-cas gf2 modules.

## The target ladder

- **(T-weak)**: `M_4 < 2^(4(n-ell))` at both endpoints, all large `ell`
  (sweep 07+09: measured truth `M_4 ~ 0.6 ell^3 2^(3ell)`, so the slack is
  `2^ell/ell^3`; the implication (T-weak) => endpoint must be re-proved
  in-house before anything else leans on it — task M1).
- **(E2') + (S)** (sweep 08): `sum_F c_F^2 <= N_points` (sign-free
  four-point count) plus absolute-constant square-root cancellation of the
  Arf-sign family.
- **(GHC-W)**: a global-hypercontractivity-type inequality for the
  mixed-cyclic Witt grading of `G_ell` (KLLM 2023 is the nearest tool;
  required constant vs sharp two-point value is the knife edge).
- Ladder discipline: L0 exact measurement -> L1 proved identity ->
  L2 surviving candidate inequality (tested to falsification effort) ->
  L3 proved graded/partial inequality -> L4 bridge. A rung is claimed only
  with its evidence class stated.

## Rules of the project

1. **Axeyum-exclusive tooling**: all computation through the repo's CAS /
   solver stack. New native operations are ADDED as new example files
   `crates/axeyum-cas/examples/acb_*.rs` (cargo auto-discovers examples;
   never edit existing source files — another lane is active in
   `gf2_hayes.rs`). External tools only as verifiers: Lean to check
   exported artifacts, z3 to double-check SMT artifacts, sympy to
   double-check CAS outputs. A cross-check disagreement is a finding,
   not an embarrassment; record it.
2. **Shared checkout hygiene**: write only inside this directory and new
   `acb_*` example files. No mutating git commands. Bounded compute
   (<~5 min, <~2 GB per run; /tmp is a nearly-full tmpfs).
3. **Epistemics (project law)**: finite computation is evidence, never a
   theorem. Every claim is labeled PROVED (with argument) / REFUTED (with
   witness) / OPEN. Web literature is fetched and verified, never recalled
   from memory; record what a paper actually proves.
4. Every workstream keeps a diary file here, named `NN-<slug>.md`,
   ending in a FINDINGS section.

## File plan

- `00-charter.md` (this file)
- `01-lit-hypercontractivity.md` — hypercontractivity classical + global
- `02-lit-energy-fourth-moments.md` — energy / moments / designs / MS boundary
- `03-lit-galois-ring-fourier.md` — Z/2^k-valued and Witt Fourier analysis
- `04-weak-target-verification.md` — (T-weak) implication re-proof + data
- `05-resurrection-audit.md` — ell-scaling of previously refuted shortcuts
  against the weak allowance
- Later phases: `1x-angle-*.md`, `2x-ladder-*.md`, `3x-theorem-*.md`.
