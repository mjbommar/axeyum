# ADR-0048: CHC/PDR engine — verify-guarded inductive-invariant discovery, MBP deferred

Status: accepted
Date: 2026-06-22

## Context

CHC / Constrained Horn Clauses with a PDR/Spacer-style engine (unbounded
invariant discovery) is the single biggest categorically-missing capability vs
Z3 ([P4.6](../../plan/track-4-usecases-frontend/P4.6-chc-horn.md), the gap audit
in [PLAN.md](../../../PLAN.md)). It is the step beyond axeyum's existing
*bounded* BMC and *fixed-depth* k-induction: it **discovers** an inductive
invariant rather than requiring the user's property to already be k-inductive.

A readiness audit (2026-06-22) found the full Spacer core is **not** startable as
specified: it needs (1) **model-based projection (MBP)** for LIA/LRA — entirely
absent from the tree (P2.6-T2.6.6 unimplemented) — for the predecessor /
proof-obligation generalization, and (2) an **online incremental LRA theory
solver** across frames (the warm `IncrementalBvSolver` is BV/Bool only). What
*is* ready: all five interpolants (P3.8), the `TransitionSystem`/BMC/k-induction
machinery (`bmc.rs`), the warm BV incremental solver with unsat-core cube
extraction (`check_assuming_core`) and `block_model`, the e-graph keystone, and
the `certify_safety_k_induction` certificate precedent.

The question this closes: **how do we start CHC soundly now, without MBP and
without an online LRA solver?**

## Decision

**Start CHC with a single-predicate IC3/PDR engine over the existing
`TransitionSystem` interface (QF_BV/Bool), in which the PDR search is entirely
untrusted and a `Safe` verdict is admitted only when the *discovered* invariant
independently passes the three inductive-invariant implication checks.** MBP and
the online LRA theory solver are deferred; the LRA/LIA constraint theories and
the multi-predicate (non-linear) Horn core follow once MBP (P2.6-T2.6.6) lands.

Concretely (`prove_safety_pdr` / `prove_safety_pdr_certified`):

- **Engine.** Classic IC3/PDR over frames `F[0]=init, F[1], …` of blocking
  clauses, proof-obligation queue, relative-inductiveness blocking, unsat-core
  inductive generalization (`check_assuming_core`), forward clause propagation,
  and a frame-equality fixpoint — all over the warm `IncrementalBvSolver` /
  `check_auto`. No interpolation or MBP dependency (so it is robust and
  self-contained); interpolation-based generalization is a later enhancement.

- **Soundness anchor (the whole point).** The search is untrusted. A `Safe`
  verdict requires the candidate invariant `Inv` (the conjunction of the
  fixpoint frame's clauses) to pass **three independent `check_auto`-unsat
  checks**: initiation `init(s) ∧ ¬Inv(s)`, consecution
  `Inv(s) ∧ trans(s,s') ∧ ¬Inv(s')`, and safety `Inv(s) ∧ bad(s)`. Any
  non-`Unsat` outcome ⇒ `PdrOutcome::Unknown`, never `Safe`. A `Reachable`
  verdict requires confirmation by `bounded_model_check` (a replay-checked
  counterexample trace). Every resource cap degrades to `Unknown`. So a PDR bug
  can only cause an over-eager `Unknown`, never a wrong `Safe`/`Reachable` — the
  same conservative-slicing + verify-before-return discipline used for the
  interpolation engine ([ADR-0047](adr-0047-craig-interpolation-proof-based.md)).

- **Certificate.** `prove_safety_pdr_certified` bundles the discovered invariant
  with the three implication proofs (`export_qf_bv_unsat_proof`), each
  DRAT-re-checkable via `recheck()` — cloning the `SafetyCertificate` precedent
  (the phase plan's `CertifiedChcSafe`).

## Evidence

- The readiness audit located every reused API (`TransitionSystem`/BMC at
  `bmc.rs:46/130/321/462`, `IncrementalBvSolver` at `incremental.rs`,
  `check_auto`) and confirmed the MBP absence.
- Tests: a safe but **non-k-inductive** property (k-induction returns
  `Inconclusive`, PDR discovers the invariant — the genuinely new capability),
  an unsafe system (BMC-confirmed `Reachable`), a k-inductive sanity case, a
  resource-capped `Unknown`, and the certified variant's `recheck()`.

## Alternatives

- **Wait for MBP and build the full Spacer core first.** Rejected: MBP is a large
  independent task; a sound BV-PDR slice delivers the headline new capability
  (invariant *discovery*) now and de-risks the engine shape. MBP is the next
  prerequisite, tracked explicitly.
- **Trust the PDR fixpoint as `Safe` without re-checking the invariant.**
  Rejected: a generalization/propagation bug could report a non-inductive frame
  as an invariant — a wrong `safe`. The three-query re-check is cheap relative to
  the search and makes the search untrusted.
- **A full multi-predicate `HornClause` IR first.** Deferred: the single-predicate
  transition-system special case reuses the existing trait and recovers BMC as a
  sub-case; the general Horn IR (T4.6.1) follows.

## Consequences

- New capability: invariant discovery beyond bounded/k-inductive reachability,
  with self-checked certificates — extends the moat (self-checking evidence).
- Next prerequisite, now the long pole: **MBP for LIA/LRA (P2.6-T2.6.6)**, which
  unblocks LRA-theory CHC and Spacer-style predecessor generalization; then the
  online LRA theory solver, the multi-predicate Horn IR, and interpolation-based
  generalization. Tracked in STATUS / P4.6.
- Adds the `prove_safety_pdr*` public surface to `axeyum-solver`; a capability
  ledger row (reachability, `Checked` — the invariant carries re-checkable
  proofs) accompanies the implementation.
