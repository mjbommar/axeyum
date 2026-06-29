# Fuzzing the protocol toolkit + two-peer protocols — design note

> **Status:** design note (2026-06-29). Two consumer-side extensions to the
> [protocol toolkit](protocol-toolkit.md), both with **no solver-internals
> changes**: (1) a concrete-execution **fuzzing oracle** that cross-checks the
> toolkit's symbolic verdicts — closing the *"formal verification **and**
> fuzzing"* pairing the goal names; and (2) verifying **two-peer** protocols
> (the real network shape) by encoding a product of two FSMs into one `BV8` state.

## 1. Fuzzing ⟷ proof, for protocols

The toolkit proves protocols symbolically (`prove_for_all_traces`, `find_bug`).
The goal asks for *fuzzing* too — and the two belong together as the cheap/expensive
ends of one dial (exactly the [spec-as-oracle gradient](verified-systems-and-protocols-scoreboard.md#fuzz--proof-gradient-spec-as-oracle)
already shown for checksums, now for control state):

- **The concrete oracle** is trivial and exact: run the FSM's own `step` table over
  a random event sequence from `init`, checking bad-set membership at each step.
  No solver, sub-microsecond per trace, a deterministic LCG (no `rand` dependency).
- **The soundness cross-check (DISAGREE = 0):** fuzzing a machine the prover called
  **`Safe`** must **never** reach a bad state — if it did, the proof would be
  wrong. Fuzzing a machine the prover called **`Reachable`** **should** hit the bad
  state within a modest bound — corroborating the bug. Concrete execution and the
  symbolic proof are independent oracles for the same property; their agreement is
  the soundness floor, mirroring `#[verify]`'s reproduce-the-witness floor.

This makes the toolkit a *"fuzz it in microseconds, prove it in milliseconds, and
they never disagree"* tool — the natural workflow for iterating on a protocol.

```rust
impl<F: Fn(u8,u8)->u8> Fsm<F> {
    fn run_concrete(&self, events: &[u8]) -> u8;          // execute the table
    fn reaches_bad(&self, events: &[u8]) -> bool;          // any prefix in `bad`?
}
// fuzz: for many random traces, assert reaches_bad == false on a Safe machine.
```

## 2. Two-peer protocols by product encoding (no toolkit change)

Real protocols run between **two** peers — a TCP handshake is the client *and*
the server. The interesting safety properties are about their *joint* state ("the
server is never `ESTABLISHED` while the client is still `CLOSED`" — the half-open /
spoofing hazard).

A product of two machines with ≤ `K` states each has ≤ `K²` joint states; for
`K ≤ 15` that is ≤ 225 < 256, so **the product fits in the toolkit's single `BV8`
state** with `state = client * K + server`. The `step` closure decodes
`(client, server)` from the combined value, applies each peer's transition for the
delivered event (e.g. a `DELIVER_SYN` event advances the server; a `DELIVER_SYNACK`
advances the client), and re-encodes. The bad-state set is the set of *encoded*
joint states that violate the interaction invariant. Everything else — the
unbounded proof, the fuzzing oracle — works unchanged.

So two-party protocol verification needs **zero new toolkit machinery**: it's a
cleverly-encoded `step` plus a bad-state list. This is the "how far does the simple
toolkit go" result — to genuine multi-party protocols.

### The two-peer handshake (Iteration 19)

- Peers: client and server, each `CLOSED`/`SYN_SENT|RCVD`/`ESTABLISHED` (≤ 4 states).
- Events = message deliveries (`SEND_SYN`, `DELIVER_SYN`, `DELIVER_SYNACK`, …),
  delivered nondeterministically (lossy/reorderable channel).
- **Invariant:** the server only reaches `ESTABLISHED` after the client sent a SYN —
  no half-open connection from a spoofed/blind SYN-ACK. Encoded as the set of joint
  states `(client=CLOSED, server=ESTABLISHED)`.
- Correct delivery rules → **Safe for all traces**; a buggy rule that lets the
  server establish on a bare delivered SYN-ACK → **Reachable** (a desync trace),
  caught by *both* PDR and the fuzzing oracle.

## Limits

- Product encoding is bounded by `BV8` (≤ 256 joint states): two ≤15-state peers,
  or three ≤6-state peers. Larger products need a wider state var (a one-line
  toolkit change to `BV16`) — out of scope here.
- Fuzzing is a *cross-check*, not a proof: it can corroborate `Safe` (no trace
  found) and confirm `Reachable` (trace found), but only the symbolic proof gives
  the all-traces guarantee. The value is fast feedback + an independent soundness
  witness.

## Plan

- Iteration 18: `run_concrete` / `reaches_bad` + deterministic-LCG fuzz tests over
  the handshake and capability machines (safe survive, buggy caught); benchmark
  fuzz-vs-proof.
- Iteration 19: the two-peer handshake product FSM, proven unbounded + fuzzed;
  scoreboard.
