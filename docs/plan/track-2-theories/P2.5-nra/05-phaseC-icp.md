# P2.5 · Phase C — Interval Constraint Propagation (cheap filter + transcendentals)

**Size:** M · **Depends on:** Phase A (interval arithmetic) · **Optional but
high-value** as a pruning filter and the only sound handle on transcendentals.

> ICP (Gao/Avigad/Clarke 2012; dReal, Gao/Kong/Clarke CADE-24 2013) is **sound for
> UNSAT** and gives δ-sat otherwise. Under axeyum's hard rule, **`δ-sat` ⇒
> `unknown`, never `sat`.** So ICP earns its place as (a) a cheap UNSAT refuter /
> box-pruner before the heavy oracle, and (b) the only tool for transcendental
> fragments where CAD/CAC/NLSAT don't apply.

## What it does

Variable domains are interval **boxes**. **Branch-and-prune**:
- **Prune** — HC4 / forward-backward contractors propagate each constraint to a
  fixpoint, shrinking boxes that provably contain no solution. Empty box ⇒ **UNSAT**
  on that branch.
- **Branch** — when pruning stalls, split the widest dimension and recurse.
- Terminate when a box is δ-small (would be δ-sat — we return `unknown`) or all
  branches empty (**UNSAT**, sound).

axeyum already has a spatial branch-and-bound in `nra.rs` (depth ≤ 6); Phase C
replaces its interior with proper interval contractors on the Phase-A interval
type, making the pruning tighter and sound for transcendental operators.

## Role in the tier stack

```
Phase B (linearization) ──unknown──> Phase C (ICP)
                                       ├── empty box  ──> UNSAT (sound, certificate = contraction trace)
                                       ├── δ-small box ──> unknown  (NEVER sat)
                                       └── still wide   ──> escalate to Phase D (complete oracle)
```

ICP also **contracts the boxes** handed to the Phase-D oracle, shrinking its
search — the cooperative pattern cvc5 uses (ICP lemmas inside the
abstraction-refinement loop).

## Tasks

| id | task | size | exit |
|---|---|---|---|
| T-C.1 | Interval arithmetic over exact rationals (`axeyum-poly::interval`, from Phase A T-A.7) with correct outward rounding | S–M | sound containment property tests |
| T-C.2 | HC4 forward-backward contractors for `+,−,·,/,pow` | M | contractor fixpoint matches a reference on test constraints |
| T-C.3 | Branch-and-prune driver; replace `nra.rs` B&B interior | M | tighter pruning; no `sat` from δ-sat (audit) |
| T-C.4 | Transcendental contractors (`sin,cos,exp,log`) — UNSAT-only | M | transcendental UNSAT decided; `sat`→`unknown` |
| T-C.5 | Feed contracted boxes into Phase D as the initial covering region | S | measured search-space reduction for the oracle |

## Soundness audit (mandatory)

A dedicated test asserts that **no ICP path ever returns `sat`** — every
satisfiable-looking outcome is `unknown` unless an exact witness is independently
constructed and replayed. This is the single most important guard in Phase C.

## Exit criteria

- ICP contractors prune boxes soundly; UNSAT branches carry a contraction-trace
  certificate; δ-sat strictly maps to `unknown`.
- Transcendental UNSAT instances that Phase B couldn't touch are now decided.
- Measured: Phase D invoked on smaller boxes (search reduction), and no
  decide-rate regression elsewhere. `nra_differential_fuzz` DISAGREE=0.
