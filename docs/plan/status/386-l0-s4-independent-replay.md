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

Detail moved to [`../notes/386-l0-s4-independent-replay.md`](../notes/386-l0-s4-independent-replay.md).

