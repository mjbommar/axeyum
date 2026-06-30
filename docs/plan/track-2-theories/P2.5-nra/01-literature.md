# P2.5 · 01 — Literature survey: nonlinear arithmetic solving

SOTA for QF_NRA (and the machinery NIA reuses). Citations verified across dblp /
SpringerLink / arXiv / ACM DL / author pages. This is the reading list that
grounds the architecture and phase plans.

## 0. The shape of the field (read this first)

QF_NRA over real-closed fields is **decidable** (Tarski 1951) but the only
*complete* methods route through **Cylindrical Algebraic Decomposition (CAD)**,
which is **doubly-exponential** in the number of variables — and that blow-up is
intrinsic (Davenport & Heintz, *J. Symbolic Computation* 5(1–2):29–35, **1988**).
So every competitive SMT solver is a **layered portfolio**: cheap *incomplete*
methods first (incremental linearization, ICP, subtropical), a complete
CAD-based engine (NLSAT/MCSAT or CAC) only as the sparingly-invoked fallback —
all inside a CDCL(T) loop. axeyum's plan mirrors this exactly.

## 1. Cylindrical Algebraic Decomposition (the complete core)

| Paper | Authors | Venue | Year |
|---|---|---|---|
| QE for RCF by CAD | Collins | LNCS 33, 134–183 | 1975 |
| Partial CAD for QE | Collins, Hong | JSC 12(3):299–328 | 1991 |
| Improved projection operator | Hong | ISSAC '90, 261–264 | 1990 |
| Improved projection (reduced) | McCallum | thesis; *QE and CAD* (Springer) | 1984/1998 |
| Improved projection ("reduced McCallum") | Brown | JSC 32(5):447–465 | 2001 |
| Improved projection (Lazard) | Lazard | *Algebraic Geometry & Its Applications* | 1994 |
| Validity proof of Lazard's method | McCallum, Parusiński, **Paunescu** | JSC 92:52–69 (arXiv:1607.00264) | 2019 |
| Real QE is doubly exponential (lower bound) | Davenport, Heintz | JSC 5(1–2):29–35 | 1988 |

**Projection lineage:** Collins → Hong → McCallum (valid for "well-oriented"
polys) → Brown → Lazard (no coordinate assumption; validity finally proved 2019
via *Lazard delineability*). This projection machinery is reused cell-by-cell by
**both** NLSAT and CAC — it is the long pole of Phase A/D. McCallum is the default;
Lazard agrees on >99.5% of QF_NRA problems and is an optional refinement.

Full CAD itself (QEPCAD B, Mathematica `CylindricalDecomposition`, Redlog,
SyNRAC, RegularChains) targets full QE / RCF, **not** the SMT QF_NRA workload —
which deliberately avoids constructing a full CAD.

## 2. NLSAT / MCSAT (Z3's complete engine)

| Paper | Authors | Venue | Year |
|---|---|---|---|
| Solving Non-linear Arithmetic (NLSAT) | Jovanović, de Moura | IJCAR 2012, LNCS 7364, 339–354 | 2012 |
| A Model-Constructing Satisfiability Calculus | de Moura, Jovanović | VMCAI 2013 | 2013 |
| Design & Implementation of MCSAT | Jovanović, Barrett, de Moura | FMCAD 2013 | 2013 |

**Mechanism:** one trail interleaving Boolean decisions (CDCL literals) and
**semantic decisions** that assign a concrete **real algebraic number** to an
arithmetic variable from its current **feasible set** (variables assigned in
"stages"). For each constraint, root isolation + interval arithmetic over
algebraic numbers compute the variable's infeasible intervals; literals are
real-propagated. A **conflict** = empty feasible set. The **explain** step applies
**CAD projection** (McCallum default, Lazard optional) onto the assigned lower
variables, producing root atoms / sign constraints that characterize the CAD
**cell** around the sample — learned as a clause that excludes the *whole cell*,
driving CDCL backjumping. Implemented in Z3 `src/nlsat/`.

## 3. Cylindrical Algebraic Coverings (cvc5's complete engine — our likely target)

| Paper | Authors | Venue | Year |
|---|---|---|---|
| Deciding NRA consistency with conflict-driven search using CAC | Ábrahám, Davenport, England, Kremer | JLAMP 119 (arXiv:2003.05633) | 2021 |
| Cooperating techniques for NRA in cvc5 | Kremer, Reynolds, Barrett, Tinelli | IJCAR 2022, LNCS 13385 | 2022 |
| On the implementation of CAC for SMT | Kremer, Ábrahám, England, Davenport | SYNASC 2021 | 2021 |
| Levelwise construction of a single CA cell | Nalbach, Ábrahám, Specht, Brown, Davenport, England | JSC (arXiv:2212.09309) | 2023/24 |

**Mechanism:** a covering-based alternative to building a full CAD. Extend a
sample variable-by-variable; when a partial sample can't be extended to a full
satisfying point, use the *reasons* (CAD projection) to exclude a whole
cylindrical cell / unsat **interval** around the sample. Excluded intervals
accumulate into a **covering of the real line per variable**. **SAT** when a full
sample is found; **UNSAT** when exclusions cover the whole line at some level —
i.e. conflict-driven **single-cell construction**, computing only the cells
needed. The **levelwise** line (Nalbach et al., SMT-RAT) is the modern shared
cell-characterization engine both CAC and NLSAT depend on. cvc5 combines CAC with
incremental linearization in an abstraction-refinement loop; CAC's 2021 SMT-COMP
win was the first non-MCSAT QF_NRA win since 2013.

> **Why CAC over NLSAT for axeyum** (see [02-architecture.md](02-architecture.md)):
> smaller implementation surface (no SAT-trail integration), the covering is a
> cleaner *checkable certificate* object for the trust ledger / Alethe (Track 3),
> and it is a more tractable greenfield build. Both reuse the same Phase-A
> projection + algebraic-number core, so the choice is reversible.

## 4. Incremental linearization (the cheap front layer — MathSAT)

| Paper | Authors | Venue | Year |
|---|---|---|---|
| Incremental Linearization for SAT & verification modulo NRA + transcendentals | Cimatti, Griggio, Irfan, Roveri, Sebastiani | ACM TOCL 19(3):19 | 2018 |
| Invariant checking of NRA transition systems via reduction to LRA+EUF | same | TACAS 2017 | 2017 |
| SMT modulo transcendental functions via incremental linearization | same | CADE-26 2017 | 2017 |
| Experimenting on solving NIA with incremental linearization | same | SAT 2018 | 2018 |

**CEGAR loop:** (1) abstract every nonlinear multiplication / transcendental as an
**uninterpreted function over LRA+EUF**; (2) solve with the mature LRA+EUF engine;
(3) UNSAT ⇒ original UNSAT (sound); (4) model found ⇒ check against real nonlinear
semantics — consistent ⇒ SAT, else add **lemma instances** excluding the spurious
model, repeat. **Sound but incomplete** — returns `unknown` when it can't refine.

**Lemma schemas** (product `x*y` abstracted as `f_mul(x,y)`):
- **Zero:** factor 0 ⟺ product 0.
- **Sign:** product sign from factor signs.
- **Commutativity:** `f_mul(x,y) = f_mul(y,x)`.
- **Monotonicity:** product monotone in factor magnitudes.
- **Tangent-plane** (the central refinement): instances of the tangent-plane axiom
  for `x*y` at the spurious model's factor values — exact on the linearization
  point, bounding elsewhere; all model-falsified instances added.

For transcendentals: **tangent-line** + **secant-line** piecewise-linear bounds
chosen numerically to stay sound under irrationals, plus basic sign/monotonicity/
known-value lemmas. (Exact algebraic forms: read TOCL 2018 §§ verbatim — the
survey synthesized them from consistent prose.)

This directly generalizes axeyum's current `x*x` / even-power handling and the
McCormick/SOS lemmas already in `nra.rs`. **Highest-leverage first increment**
(Phase B).

## 5. Interval Constraint Propagation / dReal (the transcendental specialist)

| Paper | Authors | Venue | Year |
|---|---|---|---|
| δ-Complete decision procedures for SAT over the reals | Gao, Avigad, Clarke | IJCAR 2012 | 2012 |
| Delta-decidability over the reals | Gao, Avigad, Clarke | LICS 2012 | 2012 |
| dReal: an SMT solver for nonlinear theories over the reals | **Gao, Kong, Clarke** | CADE-24 2013 | 2013 |

**Mechanism:** ICP is the theory solver in DPLL(ICP). Domains are interval
**boxes**; **branch-and-prune** alternates pruning (HC4 forward-backward
contractors tighten to fixpoint, removing sub-boxes with no solution) and
branching, until a box is δ-small (→ **δ-sat**) or empty (→ **UNSAT**).

**Critical for axeyum:** ICP is **sound for UNSAT** but **`δ-sat` is NOT a true
sat** — a δ-perturbation is satisfiable. Under our hard rule (every `sat` must be
model-checkable against the original term), **`δ-sat` maps to `unknown`, never
`sat`**. ICP's only trustworthy direction here is UNSAT, and it is the right tool
for transcendental fragments where CAD/CAC/NLSAT don't apply.

## 6. Specialist methods (feature-gated / preprocessing)

- **Virtual substitution (VS):** Weispfenning, JSC 5(1):3–27, **1988** (linear);
  AAECC 8(2):85–101, **1997** (quadratic); SMT use — Corzilius & Ábrahám, FCT 2011.
  Eliminate a variable via degree-bounded symbolic test points (+ ±∞, infinitesimal
  ε). Fast for degree ≤ 2; great cheap incomplete QE/preprocessing.
- **Subtropical satisfiability:** Sturm, ISSAC 2015 (arXiv:1501.04836); Fontaine,
  Ogawa, Sturm, Vu, FroCoS 2017 (arXiv:1706.09236). Abstract a polynomial to
  exponent vectors with coefficient signs (Newton polytope); an **LP over
  exponents** finds a monomial-dominant point → quick **SAT witness** (a concrete
  point, hence model-checkable). Incomplete, fast, terminating; targets strict-
  inequality conjunctions (>40% of QF_NRA SMT-LIB). A cheap SAT-side filter.
- **Positivstellensatz / SOS:** Stengle, Math. Ann. 207:87–97, **1974**; Parrilo,
  Math. Prog. 96:293–320, **2003** (SOS ⟺ SDP feasibility); Lasserre, SIAM J.
  Optim. 11(3):796–817, **2001**. Proves **UNSAT** via a positive-combination
  certificate. Needs an SDP solver (numerical/C dep) ⇒ feature-gated; the SOS
  multipliers / Gram matrix are **re-checkable in exact rational arithmetic** —
  axeyum already reconstructs degree-2 SOS to kernel-checked Lean, so this is the
  seed of certified nonlinear `unsat`.

## 7. Supporting machinery (Phase A)

- **Multivariate polynomial representation:** *distributed* (list of
  (coeff, exponent-vector); best sparse) vs *recursive* (univariate in one var
  with polynomial coeffs; best dense / for CAD). Survey: *Mathematics* 7(5):441,
  2019. Plan: start distributed-sparse, add recursive for projection.
- **Resultants & subresultant PRS** (CAD projection, gcd, squarefree): Collins,
  *J. ACM* 14:128–142, 1967; Brown & Traub, *J. ACM* 18:505–514, 1971; Brown,
  *ACM TOMS* 4:237–249, 1978; **Ducos, *J. Pure & Appl. Algebra* 145(2):149–163,
  2000** (the standard fast chain — implement this).
- **Real algebraic numbers:** isolating interval + defining polynomial; sum/product
  via resultants. Canonical: **Basu, Pollack, Roy, *Algorithms in Real Algebraic
  Geometry*, Springer (2006).** **Thom encoding** (derivative signs identify a
  root): Coste & Roy, JSC 5:121–130, 1988. axeyum's `Value::RealAlgebraic` is the
  starting point.
- **Real root isolation / sign determination:** **Sturm sequences** (1829);
  Budan–Fourier; **Descartes/Vincent → VCA** (Collins & Akritas, SYMSAC '76) and
  **VAS** continued-fractions (Akritas, Strzeboński, Tsigaridas, ESA 2006 — faster
  in practice). axeyum already has single-variable Sturm-based isolation.

## 8. What the SMT-COMP winners actually run

- **cvc5** — CAC + incremental linearization (abstraction-refinement). (cvc5
  system: Barbosa et al., TACAS 2022; NRA: Kremer et al., IJCAR 2022.)
- **Z3** — NLSAT (MCSAT + CAD explanations) + arithmetic tactics.
- **Yices2** — MCSAT via **libpoly** (C, Jovanović/Dutertre) + CUDD. Won 2016.
- **MathSAT5** — incremental linearization (Cimatti et al., TACAS 2013).
- **SMT-RAT** — modular C++: VS / CAD / Gröbner / subtropical / SOS + an MCSAT
  module, composed by strategy. Won quantified NRA 2024.

Recent QF_NRA single-query: 2021 cvc5 (first non-MCSAT win since 2013), 2022 cvc5,
2023 Z3++/cvc5.

## 9. Rust-ecosystem reality (this shapes the build, hard)

- **Available pure-Rust:** SAT (`batsat`, `splr`; `varisat` = only DRAT/LRAT but
  unmaintained; `rustsat` uniform interface w/ pure-Rust BatSat) — already our
  stack. Arbitrary-precision int/rational: **`num-bigint`, `num-rational`**.
- **C-backed → disqualified from the default build** (hard rule): `rug` /
  `gmp-mpfr-sys` (GMP/MPFR), `rug-polynomial`; **libpoly is C with no maintained
  Rust binding** — so the Yices2/cvc5 shortcut of "just link libpoly" is closed to
  us.
- **Absent in pure Rust — must be built from scratch:** real algebraic numbers,
  resultants/subresultants, CAD/coverings, Gröbner, virtual substitution,
  NLSAT/MCSAT explanation. **This is precisely why Phase A is the multi-month long
  pole** — and why building it well (the `axeyum-poly` crate) is the single most
  important decision in this program.

## 10. Two soundness watch-items (axeyum-specific, non-negotiable)

1. **`δ-sat` (ICP) and any subtropical/numerical near-miss ⇒ `unknown`, never
   `sat`.** Only model-checkable concrete witnesses may be surfaced as `sat`.
2. **SOS / SDP certificates must be re-checked in exact rational arithmetic**, never
   trusted from a floating-point SDP solver.
