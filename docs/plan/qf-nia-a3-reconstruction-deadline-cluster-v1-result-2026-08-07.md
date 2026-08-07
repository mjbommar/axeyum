# QF_NIA A3 reconstruction-deadline cluster v1 result — 2026-08-07

## Verdict

Reject the two-case reconstruction-deadline cluster as an implementation
population. The diagnostic found one shared terminal symptom but no shared,
actionable model-construction mechanism: both selected integer slices reached
reconstruction only after the query-global deadline, both exceeded the dense
Gomory size guards, and branch-and-bound therefore executed zero nodes. A cap
increase, fresh deadline, reserved time slice, or route-order change would be a
policy guess rather than a measured repair and is not authorized.

Temporary diagnostic code is removed after this result. No solver verdict,
public API, cap, deadline, route order, or retained benchmark score changes.
The next A3 slice returns to direct causal attribution instead of forcing a
fixture-shaped optimization.

## Exact boundary

The retained baseline and diagnostic source parent are clean integrated
`bd413357cd967aed0f2f5a1281ca0a6a8f9a276b`. The ordered target and control
lists remain bound by SHA-256:

- targets: `86e5d82a31a95b8b651314a379ffeaf2a2c3957f66c0354984bbb3ebf32bd7fb`;
- controls: `cf8d03e83b237aeea2413bf23b317b590429c40f08e0d955e8b50824212014e3`.

The final temporary release `explain_corpus` binary has SHA-256
`ca8f59037d98ea3e429292799616894e6a8ff3fde0583fce295db7142bf6f47d`.
This identifies a local diagnostic only; it is not a retained implementation
commit.

Every production-path observation used the registered 8 GiB process ceiling,
24,000 ms per-query timeout, unchanged route order, and the ordinary release
binary. `AXEYUM_NIA_RECON_DIAGNOSTIC=1` only enabled aggregate stderr counters.
No source term or model value was recorded.

## Shared reconstruction observation

Each target produced one valid reconstruction-bound diagnostic observation:

| Target | Assertions / constraints | Variables | Tightened | Gomory rows / columns | B&B nodes / depth / variables | Terminal cause |
|---|---:|---:|---:|---:|---:|---|
| `From_T2__s1.t2__p20015_safety_0.smt2` | 1,754 / 1,754 | 560 | 90 | 1,754 / 2,874 | 0 / 0 / 0 | wall-clock deadline passed |
| `SAT14/571.smt2` | 7,254 / 7,254 | 2,641 | 592 | 7,254 / 12,536 | 0 / 0 / 0 | wall-clock deadline passed |

Both slices had zero strict rows and zero non-integral coefficients/constants.
Gomory declined before tableau construction because the existing sound dense
guards admit at most 256 rows and 1,024 columns. Branch-and-bound then polled
the already-expired shared deadline before its first node. Both rows remained
`unknown`; neither produced or replayed a SAT model.

This proves deadline starvation at the reconstruction boundary and excludes
branch selection, revisited integer states, and integral-point repair as
measured causes: none of those mechanisms ran. It does not prove that raising
the dense guards is safe, that a fresh reconstruction budget is warranted, or
that a different route would recover either target.

## Route-stability discriminator

A second temporary discriminator attempted to retain the final exact-literal
probe's root LP point and report only aggregate fractionality plus whole-vector
floor, nearest, and zero-candidate feasibility. It was verdict-neutral and
bounded, but it did not produce stable mechanism evidence. Under concurrent
host load, unchanged 24-second observations moved before reconstruction:

- `p20015`: lazy arithmetic timeout after 89 rounds;
- `571`: lazy arithmetic timeout after 27 rounds;
- `p20015`: one early conflicting probe consumed the remaining budget;
- CPU-affined `p20015`: NIA relaxation expired during refinement.

All remained `unknown`. No run reached the intended terminal probe with a root
LP point, so no rounding or repair policy is preregistered. Scheduling and
thermal sensitivity are evidence against crediting this two-row cluster as a
stable implementation population, not permission to enlarge its timeout.

## Gates and disposition

The diagnostic source compiled warning-free with all features, its release
example rebuilt successfully, `git diff --check` passed, and every observed
target verdict stayed `unknown`. Because no implementation mechanism was
selected and all temporary solver code is removed, the preregistered behavioral
control and 200-row retention runs are not authorized or necessary: there is no
solver change to retain or credit.

The durable outcome is negative but useful:

1. do not raise the Gomory row/column guards for these fixtures;
2. do not grant reconstruction a fresh or reserved deadline without a separate
   measured population;
3. do not revive exact-probe model reuse, which already recovered zero targets;
4. return A3 to direct attribution and select a stable mechanism before another
   solver-policy edit.
