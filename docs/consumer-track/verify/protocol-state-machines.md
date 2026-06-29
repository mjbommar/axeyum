# Bounded protocol state machines — Block C design note

> **Status:** design note (2026-06-29), Block C of the
> [verified systems & protocols backlog](verified-systems-and-protocols.md).
> Forward-looking; bounded guarantees only. Companion to the committed Block A/B
> examples and [measured scoreboard](verified-systems-and-protocols-scoreboard.md).

## Why this is the bridge rung

A protocol *is* a state machine: TCP's open/close (RFC 9293), a TLS handshake,
seL4's IPC endpoint / capability lifecycle. The interesting safety properties are
*temporal* — "no data is accepted before the connection is ESTABLISHED", "a
capability is never used after revocation", "the machine never enters an illegal
state". Block A/B covered single-shot data properties (rung 0–1) and bounded
loops over arrays (rung 3, memory safety). Block C is the same rung-3 machinery
pointed at **control state over a bounded event trace** — the step from "this
function is safe" to "this *protocol* is safe for any sequence of K events". It is
the direct on-ramp to rung 4 (unbounded safety via k-induction / CHC-PDR,
[ADR-0048](../../research/09-decisions/adr-0048-chc-pdr-verify-guarded-invariant-discovery.md)).

## The encoding (entirely in the shipped `#[verify]` fragment)

No new macro features. Model the machine with:

- **State** as a small unsigned int (`u8`): `CLOSED = 0`, `SYN_SENT = 1`,
  `ESTABLISHED = 2`, … An auxiliary flag (e.g. `data_accepted`) is another `u8`
  used as 0/1.
- **Event trace** as a fixed array `[u8; K]` — the adversary's input. Element `i`
  is the event delivered at step `i`.
- **Driver** = an `#[axeyum_verify::unwind(K)]`-bounded loop that, for each step,
  reads `events[i]`, computes the next state via an inline transition function
  (`match`/`if` on `(state, event)` — both in-fragment), and `assert!`s the safety
  invariant **after** the transition.

```rust
#[verify]
#[axeyum_verify::unwind(4)]
fn run(events: [u8; 4]) -> u8 {
    let mut state: u8 = 0;          // CLOSED
    let mut i: usize = 0;
    while i < 4 {
        let ev: u8 = events[i] & 0x3;   // mask events into the modeled alphabet
        state = step(state, ev);        // inline match/if, returns a valid state
        assert!(state <= 2);            // safety invariant
        i += 1;
    }
    state
}
```

`unsat` (verified) ⇒ **no event sequence of length ≤ K drives the machine out of
its invariant** — a bounded model-checking result. A counterexample is a concrete
bad trace (the array of events), reproduce-validated against the original Rust.
The loop rides the same unroll / warm-`bounded_model_check` routes the macro
already uses (`bmc.rs`, `loop_system.rs`), so depth scaling is the documented
warm-vs-unroll story.

### Invariant classes worth verifying

1. **Validity** — `state` always stays within the declared enum range. A
   transition-table bug (an unguarded `state + 1`, a wrong arm) lets it escape.
2. **Protocol safety (temporal-as-state)** — fold the temporal property into an
   auxiliary state bit: e.g. set `data_accepted = 1` only on a DATA event while
   `ESTABLISHED`; assert `data_accepted == 0` whenever `state == CLOSED`. A
   transition that accepts data too early breaks it.
3. **Illegal-transition freedom** — a designated `ERROR` state is never reached.
4. **Liveness/ordering (bounded)** — "ESTABLISHED is only reachable after passing
   SYN_SENT" is encoded with a `seen_syn_sent` bit and an assert.

These are exactly the shapes a microkernel or TCP implementation needs; the
fragment expresses them with `match`, arrays, a bounded loop, and `assert!`.

## Performance expectation

Unlike the chained-modular-subtraction miter that hit the
[perf wall](verified-systems-and-protocols-scoreboard.md#measured-finding--the-equivalence-miter--certificate-perf-wall),
an FSM step is comparisons + small-int assignment (no multiplication, no deep
carry chains), so both the `Sat` bad-trace search and the `unsat` bounded proof
should stay fast at `u8` and modest `K`. This is a hypothesis to **measure** in
Block C (Iteration 6) and record on the scoreboard.

## Limits & the rung-4 bridge

- The guarantee is **bounded**: "safe for all event traces of length ≤ K". A
  protocol bug that needs K+1 steps is out of scope for the unroll route.
- The honest next step to *unbounded* safety (all traces) is an **inductive
  invariant** over the transition relation — the CHC/PDR engine (ADR-0048),
  gated behind interpolation (ADR-0047). The bounded FSM here is the same
  transition relation; lifting it is "find the invariant", not "re-model the
  protocol". That continuity is the point of doing the bounded version first.

## Backlog

1. **Handshake FSM** (Iteration 6): client open `CLOSED→SYN_SENT→ESTABLISHED`
   with a CLOSE reset; safe transition table verifies the validity + "no data
   before ESTABLISHED" invariants; a buggy table yields a bad-trace witness.
2. A richer **TCP open/close subset** (more states, simultaneous-open edge).
3. Lift one invariant to **unbounded** via the CHC/PDR route — the first rung-4
   result, and the first place a *protocol* property carries an inductive proof.
