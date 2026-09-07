# Lane: certificate-chain

<!-- plan-section: status -->

**What this lane is for.** The certificate chain
([family page](../families/evidence/README.md)) is whole at every stage except
two: CDCL(T) theory reasoning, where ADR-1704 defines a two-stream artifact that
until 2026-09-07 exactly ONE route emitted, and preprocessing, where the
`recheck` of array elimination and Ackermann **re-derives** rather than
interprets — which `trust.rs:89-95` names in its own words as proving
"determinism, not faithfulness", against a real shipped wrong-`unsat`.

Three deliverables, in order:

1. Move theory routes onto the native proof-producing core so a refutation
   *has* an ADR-1704 artifact, and attach the trust step where the report today
   leaves `trusted_steps` EMPTY. Per route, with its own verdict check.
2. Port the faithfulness witness (`witness_read_over_write`, ADR-1721 §7) to
   `eliminate_functions`, whose replacement half is re-derived exactly as
   arrays' was.
3. Make the trust step observable at corpus scale: `smtcomp_cli --evidence`
   prints `kind=`, `certified=`, `recheck=` and `arena=` and does NOT print
   `trusted_steps`, so "how many refutations carry an ADR-1704 step" cannot be
   counted from a sweep.

**Standing constraints.** Zero verdict changes, checked per route. A refutation
modulo N theory lemmas is graded `SatRefutationModuloTheory` and never
`SatRefutation` (ADR-1704 prohibition 2). The lemma count is a subtraction on
the artifact. `check_drat` is unchanged — the trusted base does not grow a line.
Sampled evidence stays uncertified: evidence, not proof.

Diary: [`docs/research/12-performance/certificate-chain-2026-09-07.md`](../../research/12-performance/certificate-chain-2026-09-07.md).

<!-- plan-section: landed-changes -->

| 2026-09-07 | `pending` | `euf_egraph`, `lra_theory` and `lia_theory` run the native proof-producing core instead of `CdclT` (S7b step 4), so their refutations can carry the ADR-1704 artifact. The swap immediately cost a give-up REASON, which the existing suite caught: without `CdclT`'s top-of-loop `timed_out()` check the native core propagated `x > 0 & x < 1` at a zero budget, ran a `final_check` the theory had no budget to answer, and returned `Sat` — `lia_theory` then reported `Unknown { kind: Incomplete }` where `CdclT` reported `Unknown { kind: Timeout }`, and `dpll_lia::check_with_arith_dpll` branches on that kind. `solve_native` now makes the eager check itself, with a test whose control shows the fixture is refuted without the deadline. |
