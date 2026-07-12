# LIA (quantified linear integer arithmetic) curated slice (cvc5 regress)

First **LIA** (quantified linear integer arithmetic — files carry
`forall`/`exists`) head-to-head of the high-level
`axeyum_solver::check_auto` dispatcher (`--backend solver`) against Z3 4.13.3.
Part of the **quantified** category (`quantified/UF`, `quantified/BV`,
`quantified/LIA`).

## Current solver boundary

This README originally recorded the division-opening baseline, when every file
declined before quantifier reasoning. That is no longer current: finite
expansion, e-matching, MBQI/MBP, closed-universal falsification, and targeted
counterexample-guided instantiation now run through the high-level `solve`
backend. The committed baseline JSON still records the historical 0/12 result
and must not be mistaken for current `HEAD` behavior.

## Provenance

Files are reused from the cvc5 regression suite
(`references/cvc5/test/regress`, a shallow sparse clone — `references/` is
gitignored). bitwuzla's regress root yields **0** exact-`LIA` clean files. Each
vendored file's name flattens its original `test/regress/...` path (`/` → `__`).

## Selection criteria

Same clean, parser-faithful, status-annotated filter as the other slices
(`scripts/curate-public-slice.py LIA <out>`): exact `(set-logic LIA)`, a
`(set-info :status …)` ground truth, plain `(assert …)` + `(check-sat)` only,
not `.smtv1`-derived, no incremental/exotic commands, at least one `assert`. The
exact-`LIA` match yields **12** clean files (all 12 contain `forall`/`exists`).
`:status` distribution: 4 sat, 8 unsat.

## Measurements (12 files)

Historical committed head-to-head:
`bench-results/baselines/lia-cvc5-regress-clean-quantified-solver-vs-z3-10s.json`,
`--logic LIA --backend solver --compare-z3 --timeout-ms 10000 --jobs 4`.
It records 0/12 decided and predates the quantifier landings above.

Fresh current-tree measurement on 2026-07-11, same corpus/backend/10 s timeout
with one job and corpus `:status` comparison:

- **files 12** — decided **11** (sat 4, unsat 7), unknown 0, unsupported 1,
  errors 0;
- all eleven decisions match the cvc5 regression statuses; no other row moved and
  there were no model-replay failures;
- `ARI176e1` and `issue5279-nqe` were already decided on current `HEAD`; the
  Euclidean-residue CEGQI slice adds `clock-3` and `clock-10`, and ADR-0096's
  checked identity Skolem adds `issue4849-nqe`; ADR-0097's two-candidate
  affine-growth CEGQI adds `repair-const-nterm`; ADR-0098's guarded unit-gap
  checker adds `sygus-infer-nested` with the global `z:=y+1` witness; ADR-0099's
  hierarchical nested-XOR checker adds `issue4433-nqe`; ADR-0101's exact finite
  equality partition adds `cbqi-sdlx-fixpoint-3-dd`; ADR-0107's checked
  free-Boolean universal models add `015-psyco-pp` and `psyco-196`;
- direct Z3 comparison was unavailable on the measuring host because no linkable
  `libz3` was installed. Regenerate the committed baseline and scoreboard only
  after restoring that oracle.

## Evidence audit

ADR-0095 adds a separate original-IR checker for the exact positive-modulus
Euclidean partition. ADR-0096 adds typed Skolem certificates and canonical
original-query replay for the restricted affine/reflexive `forall* exists`
slice. ADR-0097 independently checks the exact positive-slope piecewise theorem
behind `repair-const-nterm`. ADR-0098 independently re-matches the exact
positive-`or` nested unit-gap theorem and checks its global successor witness.
ADR-0099 independently checks the exact nested-XOR hierarchical-instantiation
theorem behind `issue4433-nqe`. ADR-0100 carries concrete original binder values
for false closed quantifier-free scalar universals and checks them by evaluating
the untouched body. ADR-0101 independently reconstructs and evaluates the exact
finite quotient induced by nested binder-to-constant equality predicates.
ADR-0107 carries arena-stable free-Boolean values and independently refutes the
untouched positive universal's negated closure through exact integer-ITE
lifting, source-bound LIA-DPLL, and scalable DRAT. A fresh dominance-auditor pass
over all eleven current-tree decisions reports:

- `clock-3` and `clock-10`: `UnsatIntEuclideanResidue`, certified and rechecked,
  zero trust steps;
- `ARI176e1` and `issue5279-nqe`:
  `UnsatClosedUniversalCounterexample`, certified and rechecked by original-body
  evaluation with zero trust steps;
- `issue4849-nqe`: `quantified-skolem-sat`, checked by identity substitution,
  zero trust steps and an individually dominant candidate;
- `repair-const-nterm`: `UnsatIntAffineGrowth`, certified and rechecked with
  zero trust steps;
- `sygus-infer-nested`: `quantified-skolem-sat`, checked against the untouched
  original nested assertion, zero trust steps and an individually dominant
  candidate;
- `issue4433-nqe`: `UnsatIntNestedXor`, certified and rechecked against the
  untouched original assertion with zero trust steps;
- `cbqi-sdlx-fixpoint-3-dd`: `UnsatEqualityPartition`, certified and rechecked
  over the untouched original nested formula with zero trust steps;
- `015-psyco-pp` and `psyco-196`: `sat-model`, checked against the untouched
  assertions by ADR-0107's source-bound Boolean/LIA closure, zero trust steps and
  individually dominant candidates;
- evidence certified **11/11**, evidence recheck completed **11/11**, audit errors 0,
  timeouts 0;
- ADR-0102 reconstructs `ARI176e1` and `issue5279-nqe` by applying the original
  universal to the checked Int/Bool witnesses and closing with kernel-checked
  integer normalization, not a certificate-refuter axiom;
- ADR-0103 reconstructs `issue4433-nqe` with two outer pivot applications, one
  adjacent nested application, and kernel-checked Iff/integer reasoning;
- ADR-0104 adds one explicit standard Euclidean-decomposition theorem to the
  trusted integer prelude, then eliminates its quotient/remainder witnesses to
  reconstruct `clock-3` and `clock-10` without div/mod proof operations or
  query-specific witness axioms;
- ADR-0105 reconstructs the full checked affine-growth class behind
  `repair-const-nterm` through guarded exact `ite` semantics, Euclidean
  decomposition, positive-slope monotonicity, and two constructive consecutive
  instances, with no new axiom;
- ADR-0106 reconstructs the single-pivot equality-partition class behind
  `cbqi-sdlx-fixpoint-3-dd` while preserving genuine Bool/Int quantifiers. It
  uses `Bool.rec` and explicit integer equality decidability rather than
  trusting the finite evaluator or its expanded quotient;
- Lean checked **7/7 UNSAT** and all **9/9 current decisions are individually
  dominant candidates** at the ADR-0106 checkpoint;
- after ADR-0107, all **11/11 current decisions are individually dominant
  candidates**;
- ADR-0108 closes `006-cbqi-ite` with 119 source-instantiated sufficient cubes
  (maximum width 6), separate source-case and weakened-skeleton closure checks,
  and bounded genuine-quantifier Lean reconstruction;
- the completed slice is **12/12 decided and checked/certified**, **8/8 UNSAT
  Lean-checked**, and **12/12 individually dominant**, with no disagreement,
  replay failure, timeout, audit error, or trust hole.

## Remaining boundaries

No row in this committed slice remains undecided:

| Rows | Status | Actual blocker |
|---|---|---|
| `006-cbqi-ite` | unsat | ADR-0108 independently refutes every sufficient free-Boolean cube with its exact source universal instance, then refutes the weakened skeleton plus all cube blocks. Evidence has empty trust steps; the first Lean slice applies the original witness tuples and closes a bounded excluded-middle tree. |

General alternation/QSAT, function-valued countermodels, N-way Lean
reconstruction for multi-constant equality partitions, and open-context proof
sharing remain outside this corpus milestone. ADR-0109 reduces the ADR-0108
public Lean module from 151,845,067 to 2,682,977 bytes by naming repeated closed
kernel-DAG nodes, while retaining the same checked cover and `False` proof.
