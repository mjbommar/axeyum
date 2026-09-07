# The NRA cross-product admission bound: what it protects

Lane `nra-admission-bound`, started 2026-09-07. Diary; appended as work lands.

## The subject

`crates/axeyum-solver/src/nra.rs`:

```rust
const MAX_CROSS_PRODUCTS: usize = 2;
```

`check_nonlinear_abstraction` counts the **distinct-operand cross-product
monomials** of the normalized assertions
(`nra_real_root::normalized_cross_product_count`, falling back to the raw
distinct-operand product count) and, when the count exceeds 2, refuses the
generic linear-abstraction / McCormick / branch-and-bound route with
`Unknown(ResourceLimit)` — after two cheap sound pre-checks (sign/zero, then
threshold-1 monotonicity), each under a 500 ms `SIGN_REFUTE_BUDGET`.

The 2026-09-06 QF_NRA loss census attributes **62 of 77 reference-only losses
(80.5%)** to this decline, with counts up to 7,874
(`bench-results/parity-losses-20260906/QF_NRA.census.tsv`).

## Step 0 — archaeology, before any measurement of my own

The bound was introduced by `9a8b09220` (2026-06-19,
"fix(nra): deterministic cross-product admission bound — graceful unknown,
never OOM"). Its commit message is the only first-hand record of what it was
built to stop, and it is specific:

> The NRA solver OOM-killed the host on multi-variable nonlinear queries
> (e.g. a²+b²+c² ⋈ ab+bc+ca). Root cause: ≥3 distinct-operand cross-products
> generate a dense disjunctive monotonicity + sum-of-squares lemma set whose
> DPLL(T)/exact-rational LRA relaxation blows up *inside a single solve call* —
> so the per-round / per-node wall-clock checks never get a turn — and bounds do
> NOT tame it (the bounded variant SIGABRT'd at the 64 GiB cap; McCormick just
> adds more lemmas).

So the **claimed** protected resource is **memory**, not soundness and not
(directly) time. That is consistent with the code: the route is sound in both
directions independently of the bound — the abstraction is a *relaxation*
(only `unsat` transfers) and every `sat` is replayed against the original
assertions by the ground evaluator in `check_with_nra`'s outer guard. Nothing
about admission changes which verdicts are *correct*; it changes only which
are *reachable*. **Raising the bound therefore cannot introduce a wrong
verdict by construction; it can only cost memory or time.** That is the
direction question the brief asks to settle before touching the constant, and
it settles in the safe direction — but the OOM claim still has to be
re-measured, because an OOM is a host-level failure, not a graceful loss.

### Three reasons the 2026-06 claim may no longer describe the code

The measurement behind the bound is 2.5 months and several relevant commits
old. Each of these post-dates it and touches exactly the mechanism the claim
names:

1. `4c2dc2524` / `3d9be6e99` — `config.timeout` threaded into the NRA/NIA
   relaxation loops and the lazy-SMT loop. The claim's core is "the per-round
   / per-node wall-clock checks never get a turn"; deadline threading is
   precisely the repair for that.
2. `487fecea9` — pure arithmetic defaults to the generic `CdclT` spine.
   `check_with_lra_dpll_within` now tries `check_qf_lra_online_cdclt` *first*,
   with a deadline derived from the caller's. The engine the 2026-06 blowup
   was measured on is no longer the first engine the relaxation reaches.
3. `68a3c8551` — "Bound oversized exact polynomial fallback".

None of that proves the bound is stale. It means the *premise* ("the wall
clock never gets a turn") is a claim about an engine that has since been
replaced on this path, and must be re-measured rather than inherited. Per
CLAUDE.md's standing rule: verify a blocker still exists before treating it
as one, including a blocker this repository's own comments name.

### What is NOT in question

- **Soundness.** Admission gates *reachability*, never correctness. Both
  transfer arguments (relaxation-`unsat`, replayed-`sat`) are independent of
  the count.
- **That the 62 files trip it.** Measured through the front door, with a
  divergence check (0 of 72 rows divergent).
- **That squares are excluded.** Only distinct-operand cross-products count;
  `x²+y²+z²+1=0` is not gated
  (`tests/nra.rs::square_only_multivariable_is_not_gated_by_cross_product_bound`).

## The measurement plan (fixed before the data is visible)

Three questions, in order. Q1 decides whether the rest is even needed.

- **Q1 — does the blowup still happen at all?** Re-run the exact shape the
  bound was built for (`a²+b²+c² ⋈ ab+bc+ca`, three cross-products, bounded
  and unbounded) with the cap lifted, under `ulimit -v`. Outcome recorded as
  one of: aborts on the memory cap (the claim holds), exceeds the wall clock
  gracefully (the claim's *mechanism* is stale but a cost remains), or
  decides.
- **Q2 — what does it cost on the real population?** The 62 census files,
  cap-2 vs cap-lifted, at the protocol's 24 s / 8 GiB, arms interleaved,
  peak RSS recorded per file. This distinguishes "OOM guard" from "time
  guard": a file that ends at the wall clock with 200 MB resident was never
  protected by a *memory* bound.
- **Q3 — is the count the right predictor?** If the cost is real, is it
  monotone in the cross-product count, or driven by something else (variable
  count, degree, lemma count, Boolean structure)? A count cap is only the
  right instrument if the count predicts the cost.

Recorded before the run so the answer cannot be chosen after seeing it:
**the honest outcome may be that the bound is right and the 62 files need a
different route.** That is a reportable finding, not a failure of the slice.

## Log

- 2026-09-07 — archaeology above; no code touched yet. Next: Q1.
