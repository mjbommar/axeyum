# P2.5 · Phase D — The complete oracle: Cylindrical Algebraic Coverings (CAC)

**Size:** XL (the completeness keystone) · **Depends on:** Phase A (projection,
algebraic numbers, root isolation) · **Makes QF_NRA complete** behind a resource
budget.

> This is the multi-month destination. It is what makes axeyum *complete* on the
> decidable real fragment — the thing Z3 (NLSAT) and cvc5 (CAC) have and we don't.
> We build **CAC** (Ábrahám/Davenport/England/Kremer, JLAMP 2021) as primary, for
> the reasons in [02-architecture.md](02-architecture.md): smaller surface than
> NLSAT's trail integration, and a covering is a cleaner checkable certificate for
> Track 3 (Lean parity). NLSAT-style explanation is a possible later optimization.

## CAC in one paragraph

Extend a candidate real assignment **variable by variable**. At each level, for
each constraint, compute the **infeasible intervals** for the current variable
(root isolation + sign over algebraic numbers on the already-assigned prefix). If
the infeasible intervals **cover the whole real line**, this level is
unsatisfiable: use the *reasons* (CAD projection of the covering polynomials onto
the lower variables) to construct an interval that excludes the whole cylindrical
cell around the sample, and propagate that exclusion **up** a level. Otherwise,
**sample** a real algebraic number outside the infeasible intervals, assign it,
and descend. A full assignment ⇒ **SAT** (model). A covering of the whole line at
the top level ⇒ **UNSAT** (the accumulated covering is the certificate).

```
get_unsat_cover(level i):
  intervals ← ⋃ infeasible_intervals(constraint, assignment) for the i-th variable
  while intervals do NOT cover ℝ:
     s ← sample_outside(intervals)            # real algebraic number
     assign x_i ← s
     if i is last variable: return SAT(assignment)
     rec ← get_unsat_cover(i+1)
     if rec == SAT: return SAT
     else: intervals ← intervals ∪ interval_from_characterization(rec, x_i, s)   # project & exclude cell
  return UNSAT(intervals)                       # covering certificate
```

Algorithms 2/4/5/6 of the JLAMP 2021 paper; cvc5's `coverings/cdcac.{h,cpp}` is the
reference implementation, with `projections.{h,cpp}` (McCallum) and
`lazard_evaluation.{h,cpp}` (Lazard lifting). The **levelwise** single-cell
construction (Nalbach et al., JSC 2023) is the modern optimization of the
characterization step — defer it past a first correct version.

## Tasks

| id | task | key references | size | exit |
|---|---|---|---|---|
| T-D.1 | **Constraint container** — `(polynomial, sign condition, source literal)`; evaluate a constraint set over a partial algebraic assignment → infeasible interval set | cvc5 `coverings/constraints` | M | infeasible intervals correct vs. brute-force on test sets |
| T-D.2 | **Sample-outside** — pick a real algebraic number outside a set of intervals (rational when possible, else a root) | JLAMP 2021 Alg.; cvc5 `sampleOutside` | M | sampling correct; prefers rationals; deterministic |
| T-D.3 | **Characterization + interval-from-characterization** — McCallum projection of covering polynomials; required-coefficients; build the excluding interval | JLAMP 2021 Alg. 4/5/6; Phase A projection | XL | excludes the right cell on the paper's worked examples |
| T-D.4 | **CAC recursion driver** — `get_unsat_cover`; variable ordering heuristic; SAT model / UNSAT covering | cvc5 `cdcac` | L | decides QF_NRA test set completely; agrees with Z3 (differential) |
| T-D.5 | **Resource budget + `unknown`** — bound projection depth / time / poly degree; outside the budget return `unknown`, never guess | — | M | budget enforced; deterministic `unknown` past it |
| T-D.6 | **Integration** — reached from Phase B/C when they return `unknown`; consumes ICP-contracted boxes (Phase C T-C.5) | — | M | tiered dispatch; Phase D only on hard residual |
| T-D.7 | (stretch) **levelwise** single-cell construction | Nalbach et al. JSC 2023 | XL | measured projection-cost reduction |
| T-D.8 | (stretch) **NLSAT-style explanation** as an alternative explain path | Z3 `nlsat_explain`; Jovanović–de Moura 2012 | XL | optional faster conflict learning |

## Soundness & certificate

- **SAT** ⇒ a real algebraic assignment that **replays** through the ground
  evaluator (`sign_at` on every original atom). This is the model-checkable
  witness the hard rule requires.
- **UNSAT** ⇒ the accumulated **covering** + its projection chain. This is an
  independently re-checkable object: a checker re-runs the projections and verifies
  the intervals cover ℝ. → **Alethe reduction proof**
  ([P3.5](../../track-3-proof-lean/P3.5-reduction-proofs.md)) and/or trust-ledger
  entry ([P3.0](../../track-3-proof-lean/P3.0-trust-ledger.md)). This is the
  Lean-parity payoff of choosing CAC over NLSAT.
- **`unknown`** ⇒ budget/degree/time exceeded. First-class, deterministic.

## The SMT-LIB division landmine (must handle before declaring NRA "complete")

NRA is decidable (Tarski) for *polynomial* constraints — but **SMT-LIB total
division makes even NRA undecidable** (Jovanović, arXiv:2605.26181, 2026): a
non-constant `div`-by-zero is effectively an uninterpreted function that can
re-encode Hilbert's 10th. So:
- The CAC oracle decides the **polynomial** fragment. `div`/`mod` are handled by
  the existing case-split-to-polynomial encoding (`(y=0)∨(x=r·y)`) *before* CAC,
  and anything that can't be reduced to polynomials stays `unknown`.
- Document this boundary explicitly; "complete for QF_NRA" means "complete for the
  polynomial fragment, `unknown`-safe on the division-induced undecidable part."

## Exit criteria

- CAC decides the polynomial QF_NRA test set **completely** within budget;
  differential vs Z3 (`nra_differential_fuzz`) DISAGREE=0 on a large random set.
- Every SAT replays; every UNSAT carries a re-checkable covering certificate.
- Tiered dispatch: Phase D runs only on the residual Phases B/C leave; measured
  decide-rate on public QF_NRA approaches Z3/cvc5.
- ADR records the CAC-vs-NLSAT choice and the division-undecidability boundary.
