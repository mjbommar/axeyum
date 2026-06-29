# Unbounded protocol safety — rung 4 design note

> **Status:** design note (2026-06-29). The rung-4 step of the
> [verified systems & protocols backlog](verified-systems-and-protocols.md):
> from *bounded* protocol-FSM safety ("no bad state in ≤ K events", the committed
> [Block C](protocol-state-machines.md)) to **unbounded** safety ("no bad state in
> *any* trace") via an inductive invariant. This is the seL4-grade capability:
> a proof that holds for the whole infinite state space, not a depth.

## Why this rung matters

Block C verified protocol invariants by *unrolling* `#[unwind(K)]` — a bounded
guarantee. A bug needing K+1 steps escapes. Rung 4 removes the bound: prove the
invariant is **inductive** (holds initially, and is preserved by every
transition), so it holds for all reachable states regardless of trace length.
This is exactly the seL4/CompCert notion of correctness — and the place axeyum's
`unsafe`-free, certificate-bearing stack is structurally differentiated, because
the proof carries **checkable evidence** (DRAT today), which Kani/CBMC do not
produce and which a hand Z3 `(check-sat)` does not either.

## The substrate (already built in `axeyum-solver`)

`TransitionSystem` is a **trait** (`axeyum_solver::TransitionSystem`) with four
methods over an `axeyum_ir::TermArena`:

```rust
fn state_vars(&self, arena, step) -> Vec<SymbolId>;  // one symbol per state component, per step
fn init(&self, arena, s0) -> TermId;                 // predicate over step-0 state
fn trans(&self, arena, pre, post) -> TermId;         // transition relation pre -> post
fn bad(&self, arena, s) -> TermId;                   // the safety-violation predicate
```

Three unbounded engines consume it (all array-free QF_BV/Bool):

- `prove_safety_k_induction(arena, &sys, max_k, cfg) -> SafetyOutcome`
  (`Safe{k}` = k-inductive at depth k; `Reachable{steps, model}`; `Inconclusive{max_k}`).
- `prove_safety_pdr(arena, &sys, cfg) -> PdrOutcome`
  (`Safe{invariant}` — IC3/PDR *discovers* the inductive invariant, already
  re-checked by the trusted `check_auto` 3-condition gate; `Reachable`; `Unknown`).
- `prove_safety_pdr_certified(arena, &sys, cfg) -> CertifiedPdrOutcome`
  (`Safe(ChcSafetyCertificate)` — three `UnsatProof`s, `initiation` / `consecution`
  / `safety`, each DRAT-recheckable via `cert.recheck()`). **The rung-4 moat
  artifact.**

`bounded_model_check(arena, &sys, bound, cfg)` is the rung-3 contrast
(`UnreachableWithinBound` is *not* a proof).

## Encoding a protocol FSM as a `TransitionSystem`

Mirror the Block C handshake (states `CLOSED`=0, `SYN_SENT`=1, `ESTABLISHED`=2),
now as a trait impl:

- **State** = BV8 symbol(s): `state` (and an auxiliary `seen_syn_sent` BV8 used as
  0/1 for the ordering property).
- **Events are nondeterministic inputs**, modeled the standard way — as a *finite
  disjunction* in `trans`: `trans(pre, post) = ⋁_{e ∈ alphabet} (post == step(pre, e))`.
  The event alphabet is finite (4), so this is a plain QF_BV disjunction of
  `ite`-built successors; the adversary may deliver any event at any step.
- **`bad`** = the negated invariant: `state > 2` (validity), or
  `state == ESTABLISHED ∧ seen_syn_sent == 0` (ordering — established without a
  handshake).

## The three results to demonstrate

1. **Unbounded validity** — invariant `state ≤ 2` is 1-inductive, so
   `prove_safety_k_induction` returns `Safe{k}` directly: the machine never
   enters an undefined state, *for all traces*. (Contrast: Block C proved this
   only for traces ≤ K.)
2. **PDR discovers what k-induction misses** — for an invariant that is true but
   not directly k-inductive (a stuck/saturating counter shape, à la the solver's
   `StuckCounter` test), `prove_safety_k_induction` returns `Inconclusive` while
   `prove_safety_pdr` returns `Safe{invariant}` — axeyum *auto-discovers* the
   strengthening. This is the categorical capability over bounded checking.
3. **Unbounded bug detection** — the blind-injection buggy handshake
   (`CLOSED + RECV_SYNACK → ESTABLISHED`) makes the ordering `bad` reachable;
   the engine returns `Reachable{steps, model}` — an unbounded counterexample
   trace, cross-checked against `bounded_model_check`.

Plus a **certified** safe case: `prove_safety_pdr_certified` →
`CertifiedPdrOutcome::Safe(cert)` with `cert.recheck() == true` (three DRAT
obligations) — the first *protocol* property carrying an unbounded, independently
checkable proof.

## Certification status & the honest gap

The unbounded certificate is **DRAT** (initiation/consecution/safety), not yet a
Lean-kernel module — consistent with the
[measured 1/7 Lean coverage](verified-systems-and-protocols-scoreboard.md#lean-cert-coverage-the-moat-metric)
for this domain. So a rung-4 `Safe` is: *invariant discovered, re-checked by the
trusted 3-condition gate, and (certified path) carrying three recheckable DRAT
proofs*. Lifting these CHC obligations to Lean is the same reconstructor-fragment
work the scoreboard tracks. The four-constraint Pareto-dominance frame still
applies: decided + sound + pure-Rust hold; the proof leg is DRAT-strong,
kernel-Lean pending.

## Limits

- Array-free QF_BV/Bool state only (the unbounded engines' scope). Buffer/array
  protocols stay bounded (rung 3) until an array-aware CHC route exists.
- `Inconclusive` / `Unknown` are first-class and honest — k-induction may need a
  larger `max_k`, and PDR may time out; neither is ever reported as `Safe`.

## Plan (Iteration 10–11)

- `tests/protocol_unbounded.rs`: the handshake validity + ordering `TransitionSystem`
  impls; assert unbounded `Safe` (k-induction and/or PDR), the certified
  `recheck()`, and the buggy `Reachable`; plus a `StuckCounter`-style
  k-induction-`Inconclusive`-but-PDR-`Safe` case.
- Benchmark bounded BMC (increasing depth) vs the single unbounded proof; record
  on the scoreboard that the unbounded proof subsumes all depths.
