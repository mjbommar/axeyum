# An ergonomic protocol toolkit — design note

> **Status:** design note (2026-06-29). Addresses the *"natural, easy to use"*
> half of the goal: rungs 0–4 proved the **capability** exists
> ([scoreboard](verified-systems-and-protocols-scoreboard.md)); this note is about
> making it **low-ceremony** enough that a stack author would actually use it.
> Consumer-side only (a test-crate helper) — no solver-internals changes.

## The ergonomics gap

The rung-4 result (`protocol_unbounded.rs`) proves a protocol safe for all traces
— but defining the protocol took a hand-written `TransitionSystem` trait impl:
~50 lines of `arena.declare` / `arena.eq` / `arena.ite` / `arena.or` boilerplate
per machine, with the transition table open-coded as nested `ite`s and the
event-nondeterminism disjunction spelled out by hand. That is fine for *one*
demo; it does not scale to a network stack with dozens of state machines. "You
could build an OS with this" requires the *definition* to be as short as the
informal state diagram.

## The toolkit

A tiny declarative `Fsm` value compiled to a `TransitionSystem` by a generic
adapter, plus two convenience entry points:

```rust
struct Fsm<F> {
    states: u8,          // valid states are 0..states
    init: u8,            // initial state
    events: u8,          // event alphabet is 0..events (delivered nondeterministically)
    step: F,             // fn(state: u8, event: u8) -> u8   (the transition TABLE)
    bad: Vec<u8>,        // unsafe states (the safety automaton, encoded into the state)
}

impl<F: Fn(u8, u8) -> u8> Fsm<F> {
    fn prove_for_all_traces(&self) -> PdrOutcome;   // PDR: Safe{invariant} | Reachable | Unknown
    fn find_bug(&self, depth: usize) -> BmcOutcome; // bounded counterexample search
}
```

The generic `TransitionSystem` adapter does the boilerplate once:

- **state** = one `BV8` symbol per step;
- **init** = `state@0 == init`;
- **trans** = `⋁_{e < events} (state' == next_e(state))`, where `next_e(state)` is
  built automatically as a nested `ite` chain over the concrete from-states
  `0..states` using the `step` closure: `ite(state==0, step(0,e), ite(state==1,
  step(1,e), … default: state))`;
- **bad** = `⋁_{b ∈ bad} (state == b)`.

Defining + proving a protocol becomes **~10 lines** (the `step` match + the field
literal + one call), versus ~50 of arena code — and the *informal state diagram
is the code*.

## Temporal properties via state-splitting

A single scalar `state` looks limited (the rung-4 ordering property needed a
`seen` ghost bit). The standard fix: **encode the safety automaton into the
state**. "ESTABLISHED only after a handshake" becomes a distinct state
`BAD_ESTABLISHED` that the *correct* transition table never enters and a *buggy*
one does; `bad = {BAD_ESTABLISHED}`. So reachability-safety over a product state
covers the temporal properties protocols actually care about, with no ghost
plumbing in the toolkit.

## First protocols

1. **Handshake validity, declaratively** (Iteration 14): re-express the rung-4
   `HandshakeValidity` as an `Fsm` and prove it — cross-checking that the toolkit
   yields the *same* verdicts as the hand-written `TransitionSystem` (the toolkit
   adds no unsoundness).
2. **seL4-flavored capability lifecycle** (Iteration 15): states
   `EMPTY`/`ALLOCATED`/`GRANTED`/`REVOKED` plus a bad `USE_AFTER_REVOKE`; events
   `ALLOC`/`GRANT`/`USE`/`REVOKE`. Safety = *"a revoked capability is never
   used"* = `USE_AFTER_REVOKE` unreachable. The correct table makes `USE` on a
   `REVOKED` cap a no-op (stays `REVOKED`) → **Safe for all traces**; a buggy
   table routes it to `USE_AFTER_REVOKE` → **Reachable** (a concrete misuse
   trace). This is a real capability-safety property in the seL4 spirit, in ~12
   lines.

## Scope & limits

- Single scalar `BV8` state (256 states / events ≤ 256) — enough for the control
  state of most protocol/capability machines; data payloads stay out (rung-3
  array work is separate).
- Reachability safety only (`bad` is a state set). Richer relational/liveness
  properties remain hand-built or out of scope.
- Lives in the test crate as a reusable helper — it demonstrates the *workflow*
  and is the natural shape a future public `axeyum-verify` protocol API could
  take, but it is not yet a committed public API.

## Plan

- Iteration 14: implement `Fsm` + adapter + the two entry points; declarative
  handshake; cross-check vs the hand-written rung-4 verdicts.
- Iteration 15: the capability lifecycle (safe + buggy); benchmark the toolkit
  (lines-of-code reduction + proof time); record on the scoreboard.
