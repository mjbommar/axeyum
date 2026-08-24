# NoH-p2: the arbitrary-curve p = 2 Newton-over-Hodge gap

Date opened: 2026-08-20. Ad hoc project, outside the normal roadmap/gates.
Parent context: docs/research/10-cas/ac-bridge-2026-08/24-novelty-check.md
(the verified literature map). Coordinator-led: the mathematical program
below is the coordinator's own analysis; agents are instruments.

## The target

Prove NP(rho) >= HP(rho) — Newton polygon over the Kramer-Miller
ramification-defined (Swan-local) Hodge polygon — for finite characters
rho: pi_1(X) -> C_2^x of 2-power order on an ARBITRARY smooth affine curve
X over a finite field of characteristic 2. Stretch: the KMU local-to-global
contact/equality theory at p = 2.

Status of the landscape (all verified at source, see 24-novelty-check.md):
P^1/affinoids solved at all p (Zhu 2004; Liu-Wan 2009; Schmidt JNT 2023);
arbitrary curves proved only for p >= 3 (KM 1909.06905, 2006.04936; KMU
2110.08656/.08657); the p = 2 obstruction is KMU Remark 6.5, verified
verbatim: their local lattice estimate degrades to a(k) = floor((k-1)/3),
"too low for applications to the global setting". The char-2 tame
three-point map exists (Kedlaya-Litt-Witaszek), so geometry is not the
obstruction; the Dwork-analytic local estimate is.

## Coordinator's analysis of the obstruction (to be adversarially checked)

At p = 2 the Dwork/Artin-Hasse splitting theta(x) = AH(pi x) with
pi^2 = -2 has series exp(pi x - x^2 + x^4 + 2 x^8 + ...): the degree-2 and
degree-4 coefficients are UNITS (v(pi^2/2) = v(pi^4/4) = 0), so the
single-pi-graded lattice cannot certify decay better than ~1/3 per degree
— the exact source of a(k) = floor((k-1)/3). Hypothesis: the loss is an
artifact of (i) the splitting-function choice and (ii) the single grading,
not of the true U_2 spectrum.

## Attack program

- **(A) Bigraded transplant.** Schmidt's (pi,p)-adic affinoid theory proves
  the Hodge bound at p = 2 on P^1; transplant its bigraded local module
  into KMU's local-to-global glue, replacing A_{pi,P}. Deliverable: the
  precise statement of the local estimate KMU need, and whether Schmidt's
  §6 estimate implies it after bigrading.
- **(B) Better splitting functions.** Pulita's Lubin-Tate exponentials
  (rank-one solvable p-adic differential equations) classify rank-one
  characters at every p. Determine the exact coefficient-decay rate of the
  Lubin-Tate splitting at p = 2 and whether it beats 1/3; if yes, re-run
  KMU's local construction with it.
- **(C) Measure the truth.** Implement U_2 exactly on the local module
  (truncated 2-adic arithmetic) for Swan conductors s <= ~10 and Witt
  lengths m <= 3; measure the TRUE valuation profile a_true(k); compare
  floor((k-1)/3) (their certificate), floor((k-1)/2)-type (needed), and
  truth. If truth >= needed, the gap is a basis/estimate artifact and the
  proof reduces to exhibiting the right lattice — which the computation
  can locate by LLL-style search over graded bases.
- **(D) Independent check of the coordinator's obstruction analysis** and
  of the exact statement "what estimate would suffice" (from KMU section 6
  and the global sections): the needed a(k) growth rate, stated exactly.

## Rules

Shared checkout: write only in this directory plus NEW example files
crates/axeyum-cas/examples/noh_*.rs; no mutating git; bounded compute
(<5 min, <2 GB); PROVED / REFUTED (witness) / OPEN labels; literature
fetched never recalled; independent sympy cross-checks for any computation.
File plan: 01-kmu-extraction.md, 02-pulita-splitting.md, 03-u2-truth.md,
10-notes-coordinator.md, 20-verify.md (later), 30-writeup.md (later).
