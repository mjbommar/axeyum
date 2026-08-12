# QF linear A5 IDL monotonicity v1 result — 2026-08-11

## Outcome

The [preregistered](qf-linear-a5-idl-monotonicity-v1-preregistration-2026-08-11.md)
12-observation exact-binary matrix completed without a process or correctness
failure. Both historical losses reproduced as `unknown` in 3/3 isolated runs;
the new maze gain and established `lpsat-goal-18` control each retained UNSAT in
3/3. Every worker exited 0, emitted exactly one identity-matching record and zero
stderr, and ran under the inherited 8 GiB limit. The losses are deterministic
enough for mechanism-specific discrimination; they are not aggregate timing
noise. No production change or census credit is authorized.

## Identity and observations

The clean source and upstream were exact
`d0e0d6ceac779b5cc3e2c1b5f3096c77780aecf9`. The 11,859,344-byte release
binary had SHA-256
`eec4813b557165ec95afc43912ad9fc2b5400ec94db5b7134ecacd50b100867d`.
The group started at load 6.45 and ran from `2026-08-11T21:25:57Z` through
`21:31:08Z`.

- BubbleSort returned byte-identical `unknown` records in 42.96--43.00 seconds
  at 179,920--180,884 KiB peak RSS. Its legacy fallback spent its complete
  construction budget validating 4,705 atoms and never built a CNF variable.
- GraphPartitioning returned byte-identical `unknown` records in 18.04--18.05
  seconds at 27,800--28,160 KiB. The DL probe consumed its slice; the fallback
  then declined before round one at 2,199 atoms and 14,670 CNF variables.
- The maze gain retained UNSAT in 19.15 seconds and 44,612--44,788 KiB.
- `lpsat-goal-18` retained UNSAT in 23.00--23.04 seconds and
  63,176--63,700 KiB.

The compact [replay record](evidence/qf-linear-a5/failures/V2-QF_IDL-monotonicity-replay-v1.json)
retains every verdict, elapsed time, peak RSS, output digest, terminal boundary,
exit code, and shared identity. The full per-run stdout, stderr, status, and
`time -v` files remain outside the repository under
`/home/mjbommar/.cache/axeyum/a5-idl-monotonicity-v1-d0e0d6cea`.

## Decision

Proceed only with the separately preregistered
[loss-mechanism discriminator](qf-linear-a5-idl-loss-mechanism-v1-preregistration-2026-08-11.md).
The BubbleSort candidate may replace per-atom full-simplex admission checks with
equivalent linearization-only validation; the GraphPartitioning observation may
only vary the diagnostic timeout to determine whether the existing DL route has
a nearby decision boundary. Neither path may relax the pre-SAT safety boundary,
change the production timeout, or start QF_RDL.
