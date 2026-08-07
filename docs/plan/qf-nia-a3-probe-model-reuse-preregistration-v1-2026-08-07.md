# QF_NIA A3 probe-model reuse preregistration v1 — 2026-08-07

## Hypothesis and code boundary

Baseline is `c851a6a14`, including the typed reconstruction-outcome repair at
`4ff9a82c6`. The complete population remains bound by causal-census SHA-256
`2585b9627fb851b06428455eb1e0754e01083c0cb17b2c24c6404087c105203a`.

For every arithmetic DPLL candidate, `theory_conflicts_for_indices` already
calls a conjunctive theory oracle. A returned `Unsat` becomes a learned conflict,
but a returned `Sat(model)` is currently reduced to the same empty “no
conflicts” vector as `Unknown`; the model is discarded. `try_finish_sat` then
calls a model oracle on the identical theory literals. On the measured cluster,
that second solve often begins near the shared deadline and returns `Unknown`.

The hypothesis is that retaining and replay-checking a concrete model from the
first exact-literal probe avoids redundant branch-and-bound and recovers at
least one reference-SAT target without changing caps, route order, or the
query-global deadline. This is not permission to treat a probe `Unknown` as
consistent or to manufacture defaults.

## Exact experiment

Refactor the theory-probe result into three explicit outcomes:

1. `Conflict(exact_indices)` only after the oracle returns `Unsat` and the
   existing independently checkable core extraction succeeds;
2. `Model(model)` only after the oracle returns `Sat(model)` for the exact
   selected literal slice;
3. `Declined(reason)` when the oracle returns `Unknown(reason)`.

The model may be reused only for the same theory and exact ordered index slice
that produced it. Before returning SAT, the combined integer/real/Boolean model
must still replay every selected literal and every original assertion. A model
that fails either replay follows the existing typed rejection path. A declined
probe supplies no model; at the full fallback boundary it must return a typed
`Unknown`, not retry with a fresh deadline or default assignment.

No public API, IR operator, solver cap, NIA budget share, SAT seed, route order,
or proof policy changes in this experiment.

## Targets and controls

The seven score targets are exactly the reference-SAT members frozen in the
13-row cluster preregistration:

- `From_AProVE_2014__juHashMapCreate.jar-obl-10__p4943_safety_0.smt2`
- `From_AProVE_2014__juHashMapCreateContainsValue.jar-obl-11__p32598_safety_0.smt2`
- `From_AProVE_2014__juHashMapCreateIsEmpty.jar-obl-10__p1784_safety_0.smt2`
- `From_T2__s1.t2__p20015_safety_0.smt2`
- `SAT14/1051.smt2`
- `SAT14/1280.smt2`
- `SAT14/571.smt2`

The six reference-UNSAT cluster members are mandatory near-miss controls and
must remain non-SAT. The direct mechanism controls remain:

- `narrow_domain_product_system_stays_satisfiable` — replayed NIA SAT;
- `false_full_replay_candidate_is_unknown_not_backend_error` — rejected model;
- `opaque_uf_model_replay_is_unknown_not_error` — unevaluable model;
- `theory_model_preserves_decline_and_inconsistency_instead_of_defaulting` —
  no loss of typed reconstruction outcomes.

The whole-list no-loss set is all 34 sidecar rows with `axeyum ∈ {sat, unsat}`
under sidecar SHA-256
`392e6cc33423518a44015a98cb1c7fdf867ea1c33ffd1cb77f761316acb5d524`.
The ADR-0378 giant-`distinct` row remains the 8 GiB process-survival control.

## Gates and retention rule

1. Unit tests must force all three probe outcomes, prove that only the exact
   SAT model is reusable, and prove declined/inconsistent candidates remain
   `Unknown`.
2. Run the exact 13-row A/B under 8 GiB and 24,000 ms per query. Record probe
   outcome counts and original-term replay for every returned SAT model.
3. If at least one target improves and no control changes incorrectly, run the
   fresh 200-row QF_NIA list. Retain only if all 34 prior decisions remain with
   identical verdicts, every new SAT model replays, and disagreements remain
   zero.
4. If no target improves, reject probe-model reuse as an A3 breadth lever. An
   explicit outcome API may be retained only if it independently removes
   redundant work or improves typed observability without a verdict regression.

Stop on any SAT replay failure, reference-UNSAT-to-SAT change, prior-decision
loss, memory ceiling, general cap increase, new deadline, or model reuse across
a different literal slice.

