# Lane: certificate-chain

<!-- plan-section: lane-status -->

**What this lane is for.** The certificate chain
([family page](../families/evidence/README.md)) was whole at every stage except
two: CDCL(T) theory reasoning, where ADR-1704 defines a two-stream artifact that
until 2026-09-07 exactly ONE route emitted, and preprocessing, where the
`recheck` of array elimination and Ackermann **re-derives** rather than
interprets — which `trust.rs` names in its own words as proving "determinism,
not faithfulness", against a real shipped wrong-`unsat`.

**Where it stands after this lane.**

- **Five theory routes run the proof-producing core**: `dl_online` (S7b) plus
  `euf_egraph`, `lra_theory`, `lia_theory` and `string_theory`. Three do not,
  each for a named reason (below).
- **The front door attaches the step.** `produce_evidence` records the artifact
  around its whole dispatch and attaches `SatRefutation` /
  `SatRefutationModuloTheory` on the bare-`unsat` arms, behind an ambiguity
  guard that declines rather than publish a case-split branch's refutation as
  the query's.
- **The number is readable from a sweep.** `smtcomp_cli --evidence` prints
  `trusted=<n>[:<label>[+],…]`. Measured on the committed parity lists (first 40
  files, 8 s, release, `taskset -c 0-7`, zero verdicts contradicting
  `declared`): QF_IDL 3 of 3 refutations carry a step, 2 of them ADR-1704;
  QF_LIA 4 of 4 (pre-existing `farkas+`, newly visible); QF_UF 1 of 16;
  QF_LRA decided nothing at that budget.
- **The preprocessing witness is ported** to `eliminate_functions`, and porting
  it produced a finding that changed its design (below).

**What this lane did NOT reach**, stated as claims a resumer can check:

- `uflra_online` and `uflia_online` are still on `CdclT`. Both read
  `CdclT::theory_propagations()` as a diagnostic out-param; on the native core
  that counter is behind `TheorySolveOptions::collect_layer_stats`, which turns
  on per-call clock reads, so it is its own change with its own measurement.
- `ufbv_online` is still on `CdclT`: it is the single client of the incremental
  protocol, which has no port (S7a step 3).
- **QF_UF's fifteen uncounted refutations.** They arrive as
  `unsat-bool-euf-online`, whose evidence producer attaches no trusted step at
  all, so they never reach the arm that reads the artifact channel. Moving a
  route is necessary and not sufficient; the fix is an attach in
  `check_bool_euf_online_evidence`. This is the highest-value next slice.
- **The cost of dispatcher-wide recording was not priced.** Recording is on for
  every `produce_evidence` call now, bounded by the 8M-literal budget. The
  sweeps above ran without complaint at an 8 s budget, but no before/after
  timing A/B was taken. Report as "not measured", not as "free".
- `scripts/tests/test_execute_autogenesis_operation.py` was not run as a suite:
  all 15 of its tests error in `setUp` in this worktree ("frontier is stale or
  does not match the authoritative ledger"), before and after this lane. The
  regex change was verified directly instead.

**Standing constraints, all held.** Zero verdict changes, checked per route. A
refutation modulo N theory lemmas is graded `SatRefutationModuloTheory` and
never `SatRefutation`. The lemma count is a subtraction on the artifact.
`check_drat` is unchanged. Sampled evidence stays uncertified.

Diary: [`docs/research/12-performance/certificate-chain-2026-09-07.md`](../../research/12-performance/certificate-chain-2026-09-07.md).
Backing data: [`bench-results/certificate-chain-20260907/`](../../../bench-results/certificate-chain-20260907/README.md).

<!-- plan-section: landed-changes -->

| 2026-09-07 | `ea85c9813` | `euf_egraph`, `lra_theory` and `lia_theory` run the native proof-producing core instead of `CdclT` (S7b step 4), so their refutations can carry the ADR-1704 artifact. The swap immediately cost a give-up REASON, which the existing suite caught: without `CdclT`'s top-of-loop `timed_out()` check the native core propagated `x > 0 & x < 1` at a zero budget, ran a `final_check` the theory had no budget to answer, and returned `Sat` — `lia_theory` then reported `Unknown { kind: Incomplete }` where `CdclT` reported `Unknown { kind: Timeout }`, and `dpll_lia::check_with_arith_dpll` branches on that kind. `solve_native` now makes the eager check itself, with a test whose control shows the fixture is refuted without the deadline. |
| 2026-09-07 | `1777d7a8e` | `string_theory` joins them; `SatModelCtx::solver` moves from `&CdclT` to `&NativeModel`. Counts attributed by pairing each `Running tests/<file>` line with its own result — cargo runs test binaries alphabetically, not in flag order, and a first pass at the message had two suites' counts swapped. |
| 2026-09-07 | `a945efdd7` | The trust step reaches the front door, and the ledger is readable from a sweep. `produce_evidence` records around its whole dispatch; the ambiguity guard declines when more than one native refutation happened, because `auto::check_auto` enumerates case-split branches and discards each one's `Unsat` (relaxing `== 1` killed exactly one test). `smtcomp_cli --evidence` gains `trusted=`, whose position is FORCED: `execute-autogenesis-operation.py`'s regex was anchored at both ends and required `certified=` immediately before `recheck=`, so every placement broke it. Also measured: small queries never reach the bare arm — QF_UF transitivity gets `unsat-alethe`, a UF pigeonhole `unsat-bool-euf-exhaustive` — so this is a large-query metric. |
| 2026-09-07 | `7da79642f` | `witness_function_abstraction` ports ADR-1721 §7 onto `eliminate_functions`, wired into `AckermannUnsatCertificate::recheck` as step 2. **The straight port did not catch the defect it exists for.** With the elimination mutated so every application of one function shares one fresh symbol, the satisfiable `f(a) = 1 & f(b) = 2` becomes a wrong `unsat` and `recheck` still returned `Ok(true)` — the two sides are compared as BOOLEANS and both are simply `false` at almost every sample. The witness therefore carries a structural count, `unnamed_applications`; with it, `recheck` returns `Ok(false)`. Mutation controls: never incrementing that count kills exactly one test; never recording a value disagreement kills three. |
