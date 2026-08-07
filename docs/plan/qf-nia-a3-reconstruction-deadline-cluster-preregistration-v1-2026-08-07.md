# QF_NIA A3 reconstruction-deadline cluster preregistration v1 — 2026-08-07

## Selection boundary

Baseline is clean pushed `main` at
`2aa6f03ef189161aab17ad7f783aecd5d329b02f`. It contains the complete
67-row census, typed model-reconstruction outcomes, and the rejected
probe-model-reuse experiment. The population remains bound by census SHA-256
`2585b9627fb851b06428455eb1e0754e01083c0cb17b2c24c6404087c105203a` and
retained-sidecar SHA-256
`392e6cc33423518a44015a98cb1c7fdf867ea1c33ffd1cb77f761316acb5d524`.

Direct production-path attribution rebuilt release `explain_corpus` from this
baseline (binary SHA-256
`b4c55749c5cfd25c89422f3e3251cd083563d84d2cac6ab30c3c7aeed78ad77e`) and
ran the exact seven reference-SAT residuals sequentially with an 8 GiB process
ceiling, 24,000 ms per query, and no `AXEYUM_*` lever. Four rows stopped in the
lazy arithmetic search/core loop. Two rows consistently reached the typed
integer-model reconstruction boundary and exhausted the shared query deadline:

- `From_T2__s1.t2__p20015_safety_0.smt2` — reconstruction deadline in 4/4
  observations;
- `SAT14/571.smt2` — reconstruction deadline in 4/4 observations.

`From_AProVE_2014__juHashMapCreateIsEmpty.jar-obl-10__p1784_safety_0.smt2`
was reconstruction-bound in 3/4 observations but stopped in the earlier lazy
search loop once. It is therefore a load-sensitive near-miss, not a v1 score
target. This evidence preserves the handoff's stable two-case cluster rather
than silently expanding it from one favorable observation.

The exact ordered target and control files are
[`reconstruction-deadline-v1-targets.txt`](evidence/qf-nia-a3/reconstruction-deadline-v1-targets.txt)
and
[`reconstruction-deadline-v1-controls.txt`](evidence/qf-nia-a3/reconstruction-deadline-v1-controls.txt).
Their SHA-256 digests are respectively
`86e5d82a31a95b8b651314a379ffeaf2a2c3957f66c0354984bbb3ebf32bd7fb` and
`cf8d03e83b237aeea2413bf23b317b590429c40f08e0d955e8b50824212014e3`.

## Diagnostic hypothesis

For a provisionally consistent arithmetic skeleton, `try_finish_sat` extracts
the selected integer literals and invokes the plain conjunctive QF_LIA model
oracle. Both targets reach this call, and both return the same typed decline:
the exact-rational simplex relaxation plus integer branch-and-bound does not
produce a replayable integer model before the already-shared deadline. The
cause may still differ inside that boundary: Gomory may decline for different
reasons, branch selection may revisit equivalent integer states, or the LP
relaxation may expose a cheaply repairable integral point.

The first increment is diagnostic-only. Add bounded, deterministic internal
statistics for model reconstruction: collected integer variables and
constraints, tightened constraints, Gomory disposition, branch-and-bound nodes
visited, maximum depth, distinct branched variables, and terminal cause. Do not
record source terms, model values, wall-clock-dependent decisions, or change a
verdict. Remove temporary diagnostics after they identify a shared mechanism;
retain an explicit typed statistic only if it independently improves permanent
route observability.

No implementation lever is authorized until both targets exhibit the same
actionable mechanism. If they do, preregister that one mechanism before changing
search. If they do not, reject this cluster and return to direct attribution.

## Targets and controls

The two targets are declared/reference SAT and current Axeyum `unknown`. A
candidate gain counts only when Axeyum returns SAT and the model replays every
selected literal and every original assertion.

The six original reference-UNSAT members of the former 13-row replay bucket are
mandatory near-miss controls and must remain non-SAT. The load-sensitive
`p1784` row is an additional routing control: an experiment may not claim it as
a target unless a later separately preregistered population makes its
classification stable. Existing unit controls remain mandatory:

- `narrow_domain_product_system_stays_satisfiable`;
- `false_full_replay_candidate_is_unknown_not_backend_error`;
- `opaque_uf_model_replay_is_unknown_not_error`;
- `theory_model_preserves_decline_and_inconsistency_instead_of_defaulting`.

The whole-list no-loss population is all 34 retained QF_NIA decisions in the
bound sidecar. The ADR-0378 giant-`distinct` row remains the process-survival
control.

## Gates and stop conditions

1. Diagnostic instrumentation must leave the exact two targets and seven
   target/routing rows verdict-identical under 8 GiB and 24,000 ms per query.
2. Any proposed search change requires a second preregistration naming the
   measured shared mechanism, deterministic bounds, exact target/control
   outcomes, and a removal rule.
3. The two-row A/B is the first behavioral gate. At least one target must become
   replay-checked SAT and every control must remain sound before a fresh 200-row
   run is authorized.
4. Retain code only if all 34 prior decisions remain identical, every new SAT
   model replays on the original query, no disagreement appears, and resource
   limits remain within the existing 8 GiB / 24,000 ms protocol.

Stop on any SAT replay failure, reference-UNSAT-to-SAT change, prior-decision
loss, memory ceiling, query-global deadline reset, general cap increase,
route-order change, fixture-specific basename/path behavior, or diagnostic
evidence that the two targets do not share one mechanism.
