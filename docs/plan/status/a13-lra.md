# Lane: a13-lra — QF_LRA's replay wall: the tableau admission currency (ADR-2146) and the disequality split (ADR-2147)

<!-- plan-section: lane-status -->

**A13-LRA (`WIP`, a13-lra, 2026-09-17).** Stock-take queue item 2. Both
census mechanisms re-confirmed at head (`43f1e0f90`, shipped binary
`d3606850…`): 27 / 27 no-tableau rows stop at `fm-fallback-declined` at the
census screen and — the fact that sizes the first lever — **27 / 27 stop at
the ATOM SCREEN at the shipped multiplier**, every one having more than the
1,024 atoms it admits; 11 / 11 disequality rows stop at
`model-built-but-does-not-replay` at both screens, and `sc-25`'s **371 of
776** equality atoms asserted false is confirmed from the shipped route's own
probe. Two OFF levers built and committed (`0f311e650`):
`AXEYUM_LRA_ADMIT_NONZEROS` (nonzero admission + row ceiling + a RUN-TIME
fill-in cap the entry count cannot supply) and `AXEYUM_LRA_DISEQ_SPLIT`
(cvc5's model-driven split, the strict halves riding the equality's own rows;
the native core re-polls `take_new_atoms` after a `Sat` final check). Two
defects found on the way: the ADR-1704 artifact constructor panicked on a
lemma over a fresh variable (widened, pinned), and the shipped route cannot
refute `x ≠ y ∧ x ≤ y ∧ x ≥ y`. Smoke on the census family under the split:
`sc-7` unknown@24 s → `unsat` in 0.6 s, `sc-9/11/13/15/17` all `unsat`, the
larger `sc-*` and `pursuit-safety-16` still `unknown`. Five z3 fuzzes × four
env arms all green with nonzero counts; corpus_regression, `--lib lra` (162)
and `simplex` (43) green. **In flight:** the four-arm A/B (base / nz / sp /
both) on QF_LRA pinned + held-out and QF_UFLRA, two-arm DL controls, and the
screen-16 composition, on s5/s6 (`bench-results/lra-admission-diseq-20260917/`);
the mutation controls; workspace clippy. **Next:** the A/B tables, 3× mover
rechecks, the ship decision per lever, ADR status, `gen-plan`.

<!-- plan-section: landed-changes -->

| 2026-09-17 | a13-lra | `0f311e650` ADR-2146 / ADR-2147 levers (OFF), unit + soundness-negative + certificate tests, `distinct` and boundary-tableau fuzz seed classes, nine one-test mutation suites, five registry entries, the A/B harness; `e9167dd21` the sizing (`bench-results/lra-admission-diseq-20260917/`). |
