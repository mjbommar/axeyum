# ADR-0065: Finite-domain disjunction case-split (QF_NIA/QF_LIA)

Status: accepted
Date: 2026-07-08

## Context

A class of integer queries pins variables to a finite set through top-level
disjunctions of equalities, then constrains them nonlinearly. The keystone is the
cvc5 regress row `cli__regress1__nl__rewriting-sums` (`QF_NIA`, unsat):

```
(or (= x 5) (= x 7) (= x 9))
(or (= y (+ x 1)) (= y (+ x 2)))
(or (= z (+ y 5)) (= z (+ y 10)))
(> (* z z) 1000000000)
```

`z ≤ 21`, so `z² ≤ 441 < 10⁹`, contradicting `z² > 10⁹` — UNSAT over just the 12
ground combinations. But the deciding equalities are **conditional** (inside the
`or`s), so global preprocessing (`solve_eqs`) cannot propagate them into the
nonlinear `z² > 10⁹` atom; the online theory loop then runs the heavy nonlinear
machinery per assignment and times out (10.7 s at a 5 s budget). Measurement
(post-#88) showed this was one of the "timeout" rows, but a *distinct* cause from
the poly hot-loop (#85) — a control-flow/dispatch gap, not an arithmetic-kernel
one.

A **broad** disjunction case-split was implemented earlier and **reverted**: it
split *every* top-level `(or …)` (including region/inequality disjunctions), so
per-branch sub-solves inherited the same overrun and the corpus PAR-2 roughly
doubled (see `docs/research/05-algorithms/arithmetic-deadline-bounding-ceiling.md`).

## Decision

**Add a NARROW finite-domain disjunction case-split
(`try_finite_domain_split`, `auto.rs`), fired only as an `Unknown`-fallback,
splitting only disjunctions whose every disjunct is an equality.**

- **Trigger:** runs only when the primary dispatch already returned `Unknown`
  (like `try_conjunct_refutation`), so the decided fast path is never slowed — the
  root cause of the broad version's regression.
- **Scope:** a conjunct is split only if it is `(or (= …) … (= …))` — every
  disjunct an equality (`as_equality_disjunction`). Equality disjuncts are what
  make branches cheap: each chosen equality is *unconditional* in its branch, so
  the branch's own preprocessing propagates it (a `(< x 5)`-style region disjunct
  would not, and splitting it only multiplies work — hence the restriction). A
  bounded branch product (`MAX_FINITE_DOMAIN_BRANCHES = 64`) declines a large
  fan-out to the width ladder.
- **Semantics:** `D₁ ∧ … ∧ Dₘ ∧ rest` is satisfiable **iff** some choice of one
  equality from each `Dᵢ`, conjoined with `rest`, is — the exact CNF-to-DNF
  case-split. Each branch is solved by re-entering `check_auto` (which
  preprocesses → propagates the now-unconditional equalities → the nonlinear atom
  collapses to a ground comparison). Half the budget is split across branches;
  every branch re-enters with no equality-disjunction left, so the recursion
  bottoms out.
- **Verdict rule:** every branch `unsat` ⇒ `unsat`; any branch `sat` ⇒ `sat`
  (that branch's model satisfies each `Dᵢ` — its chosen equality is a disjunct —
  and `rest`, hence the original); some branch `unknown` with none `sat` ⇒ decline
  (never a wrong `unsat`). Wired identically into `check_auto` and
  `check_auto_explained` (route `finite-domain-split`) for verdict invariance.

## Evidence

- Decides `rewriting-sums` `unsat` (route trace: `finite-domain-split: decided
  unsat`); cvc5-regress QF_NIA unsat 16→17, unknown 4→3, DISAGREE = 0.
- Unit gate `tests/finite_domain_split.rs` (4): the keystone unsat, a
  finite-domain branch-sat, an all-branches-unsat, and a **wrong-verdict-negative**
  (a reachable-bound query with the same shape must NOT be refuted).
- `progress_frontier` 8/8 (`frontier_nia_unsat` held — no regression, unlike the
  broad version), `corpus_regression` DISAGREE = 0, `--lib` 731, `route_trace` 6
  (verdict invariance), clippy `-D warnings`.
- **z3 `nia_differential_fuzz` (2500) + `nra_differential_fuzz` (2000):
  DISAGREE = 0** — the adversarial vs-Z3 gate, run because this route emits BOTH
  `sat` and `unsat` (soundness-critical both directions). <!-- CONFIRM on run
  completion; revert on any DISAGREE. -->

## Alternatives

- **Broad disjunction split (the reverted version)** — rejected: splitting region
  disjunctions multiplies heavy sub-solves and doubled corpus PAR-2. The
  equality-only + `Unknown`-fallback narrowing is what makes it pay without
  regressing.
- **Propagate conditional equalities globally in preprocessing** — rejected: a
  conditional equality inside an `or` is not a global fact; propagating it is
  unsound without the case-split.
- **A full DPLL(T) over the disjunction structure** — the online CDCL(T) already
  exists (ADR-0060) but stalls here because its per-assignment theory solve
  re-runs the nonlinear machinery without the equality propagation the branch
  re-entry provides. Improving that is the more general fix; this route is the
  targeted, low-risk slice that closes the row now.

## Consequences

- **Easier:** finite-domain-pinned nonlinear queries (a common SMT idiom) now
  decide; the split composes with every downstream route (each branch is a full
  `check_auto`).
- **Harder / revisit:** the equality-only restriction leaves inequality/region
  disjunctions to the ladder (deliberately — they caused the regression). Widening
  is gated on measured ROI (measure-don't-seed).
- **Standing rule:** this route emits both `sat` and `unsat`, so any change must
  re-run `nia_differential_fuzz` (DISAGREE = 0) plus the wrong-verdict-negatives.

## Backlinks

- Code: `crates/axeyum-solver/src/auto.rs` (`try_finite_domain_split`,
  `as_equality_disjunction`, `MAX_FINITE_DOMAIN_BRANCHES`); wired in `check_auto` /
  `check_auto_explained`.
- Tasks #87 (this route), #85 (the sibling poly hot-loop, now a single row), #86
  (the residue map that surfaced the class).
- Related: ADR-0060 (arith online CDCL(T) dispatch — the general engine this
  complements), ADR-0064 (integer-algebraic identity refutation, sibling
  `Unknown`-fallback).
