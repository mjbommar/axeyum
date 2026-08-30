# L0/S4 — independent proof replay

<!-- plan-section: lane-status -->

Lane: `l0-s4-independent-replay`. Phase S4 of the trusted-library safety
roadmap (ADR-0717). Decision: [ADR-0760](../../research/09-decisions/adr-0760-independent-replay-is-graded-per-declaration-by-name.md).

## Status

S4's grading discipline is landed and gating. The census executes rather than
reading claims, `missing=0` is enforced, the inheritance guard is attested by
Lean itself, and both mutation classes are rejected. Two findings came out of
it, one of which says a shipped fact claims replay it does not have.

## The measurement

One run, pinned Lean 4.30.0 (`d024af09`), whole `creal` carrier,
`cargo test -p axeyum-lean-kernel --test real_lean_replay_census`:

    population=2045 representable=1972
      theorem_type_not_prop=48 blocked_by_dependency=25
    checked=1972 expected=1972 missing=0 extra=0
    5 passed; 0 failed; finished in 240.80s

Flagship grades, each read out of the run:

| subject | Axeyum | pinned Lean |
|---|---|---|
| `CReal.ivt_approx` | accepted | **replayed** |
| `CReal.ivt_exact_root_decides_sign` | accepted | **replayed** |
| `CReal.evt_attained_max_decides_sign` | accepted | **replayed** |
| `CReal.fermat_interiorExtremum` | accepted | **replayed** |
| `CReal.rolle_interiorExtremum` | accepted | not representable — blocked by `CReal.hasDerivative_neg` |
| `CReal.mvt_interiorExtremum` | accepted | not representable — blocked by `CReal.hasDerivative_add` |

## Findings

**1. This kernel admits `Theorem`s whose type is not a proposition; Lean's
kernel refuses them.** 48 declarations, plus 25 blocked by depending on one.
`CReal.weierstrassMTest` concludes in `CReal.UniformConvergesOn`, which
`creal/uniform_convergence.rs` deliberately makes `Type`-valued so the
convergence rate is data. The declarations are intentional and the reason is
sound; what was missing is that nothing recorded them as outside what Lean will
accept **as a theorem**. Not a demonstrated soundness hole, and this lane does
not claim one — but a real gap in independent checkability, in exactly the
place ADR-0717 says to look.

**2. `real_lean_creal_carrier_kernel_replay` could not reach a verdict.** It is
registered in `scripts/check-lean-gate.sh` and was SIGABRTing on a stack
overflow before a single Lean ran (`creal` needs 16 MiB in debug; a `#[test]`
thread has 2 MiB). Measured with `RUST_MIN_STACK` unset, so not one-shell
contamination. Wrapped in `on_a_deep_stack`, it now reaches Lean and fails on
finding 1, because its claim is over the *whole* carrier.

**So `F:lean-kernel-accepts-the-whole-constructed-real-carrier` claims an
independent replay that is not currently re-derivable.** This lane touched no
fact's `epistemic_status`, `proof_route`, `axiom_footprint` or
`formal.statement`; the finding is reported for that fact's owner.

## How a sibling is prevented from inheriting a grade

`grade` is an exact membership test on the subject's own name against the set
Lean's kernel ended holding, read from `env.constants` via the new
`replay-lean4export.lean --emit-names`. Attested end to end: replaying the
closure of `CReal.ivt_step` **alone** (359 constants) grades `ivt_step`
replayed and `ivt_approx` — its own descendant, same family, same module,
reachable in one step — not-replayed.

## Mutation kill sets, as measured

| mutation | tests killed |
|---|---|
| `grade` prefix-matches instead of exact | 1 — pure guard only |
| `grade` always returns `Replayed` | 2 — both inheritance guards |
| `is_a_proposition` always `true` | 2 — census + earned typed reason |
| Lean reports zero constant names | 3 — every Lean-dependent test |

The first **survived** the Lean-attested guard: `CReal.ivt_approx` is not a
prefix of anything in `ivt_step`'s closure, so prefix matching is invisible end
to end. Recorded rather than hidden; the two guards fail on disjoint defects.

## Registration

- `real_lean_replay_census` added to `scripts/check-lean-gate.sh`'s suite
  table; its counted floor 223 → 229 for six real-Lean invocations.
- `check-lean-gate.sh` was already wired into `scripts/check.sh` and the
  justfile, so no new aggregate entry was needed.
- Monotone replay floor 1,900, 72 below the measurement. It may only rise.

## Holdout isolation

    AUTOGENESIS_HOLDOUT_ISOLATION|held_out=116|files_scanned=1109|settled=0|references=0|verdict=PASS

## What the next increment costs

1. **Decide the `Type`-valued carriers** (the natural follow-on). Exporting
   `UniformConvergesOn`/`HasDerivativeOn` theorems as `def`s would let Lean
   check all 73, recovering `rolle_interiorExtremum` and
   `mvt_interiorExtremum`. Needs an ADR — it changes what "theorem" means on
   the wire — plus ~1 day to implement and re-measure.
2. **Reconcile the carrier fact and suite** with finding 1. Small, and owned by
   that fact's lane, not this one.
3. **Extend the census beyond `creal`.** `nat`, `int`, `rat`, `complex` and
   `string` are each one more prelude build plus one Lean invocation on the
   same machinery — roughly 4 min of runtime each and a few hours of work.
   That is what moves the ledger-wide `independent_replay` figure off 8/2117;
   the 2,117 facts are not 2,117 exports, since one carrier replay grades
   every declaration in it by name.
