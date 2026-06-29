# Verified systems & protocols — measured scoreboard

Companion to [`verified-systems-and-protocols.md`](verified-systems-and-protocols.md).
Measured from the committed example suites driving the real `#[axeyum::verify]`
macro:

- `crates/axeyum-verify/tests/network_examples.rs` (Block A)
- `crates/axeyum-verify/tests/systems_examples.rs` (Block B)
- `crates/axeyum-verify/tests/protocol_fsm_examples.rs` (Block C — bounded protocol FSMs)
- `crates/axeyum-verify/tests/protocol_unbounded.rs` (rung 4 — *unbounded* protocol safety)
- `crates/axeyum-verify/tests/protocol_toolkit.rs` (ergonomic declarative FSM toolkit)
- `crates/axeyum-verify/tests/spec_oracle_gradient.rs` (the fuzz↔proof gradient)

Reproduce: `cargo test -p axeyum-verify --test network_examples --test
systems_examples --test protocol_fsm_examples --test spec_oracle_gradient --
-Z unstable-options --report-time --nocapture` (nightly for per-test times;
`--nocapture` to print the Lean-cert coverage lines). Times are a single
indicative wall-clock run (debug build, `scripts/mem-run.sh`), 2026-06-29; not
tuned.

## Headline

- **13 `#[verify]` cases**: 7 safe → **verified**, 6 buggy → **bug-found**.
- **DISAGREE = 0** (soundness floor): every safe case proves within its bound;
  every bug witness is re-run through the *original* fn and actually panics
  (`reproduce::panics_on`).
- **Lean-cert coverage (the moat metric): 1/7 safe cases (14%) carry a
  kernel-checkable Lean module; 7/7 carry a re-checked in-tree certificate.**
  See [Lean-cert coverage](#lean-cert-coverage-the-moat-metric) below.
- All guarantees are **bounded** (fixed widths / `#[unwind(K)]` / fixed array
  sizes). "Verified" = no bad state reachable within the bound, not total
  correctness.

## Per case

| Case | Domain | Rung | Class | Expected | Outcome | Width / bound | Verify time |
|---|---|---|---|---|---|---|---|
| `ic_carry_fold_equiv` | Internet checksum | 1 (equiv) | `assert_eq!` | safe | verified | u32, 16-bit values | 0.37 s |
| `ic_missing_carry_bug` | Internet checksum | 1 (equiv) | `assert!` | bug | bug-found | u32, 16-bit values | 0.002 s |
| `be16_field_roundtrip` | header parse | 1 (roundtrip) | `assert_eq!` | safe | verified | u16 | 0.012 s |
| `seq_advance_roundtrip` | TCP seq # | 1 (modular) | `assert_eq!` | safe | verified | u8 | 2.31 s |
| `naive_window_upper_overflows` | TCP seq # | 0 (overflow) | add overflow | bug | bug-found | u32 | 0.002 s |
| `ring_wrapped_read_safe` | ring buffer | 3 (loop/array) | index-OOB | safe | verified | `[u8;4]`, unwind 5 | 0.023 s |
| `ring_unwrapped_read_oob` | ring buffer | 3 (loop/array) | index-OOB | bug | bug-found | `[u8;4]`, unwind 5 | 0.005 s |
| `bounded_read_safe` | length-guarded copy | 3 (loop/array) | index-OOB | safe | verified | `[u8;4]`, unwind 5 | 0.18 s |
| `unbounded_read_oob` | length-guarded copy | 3 (loop/array) | index-OOB | bug | bug-found | `[u8;4]`, unwind 5 | 0.003 s |
| `handshake_validity_safe` | protocol FSM | 3 (state machine) | `assert!` | safe | verified | `[u8;4]`, unwind 4 | 0.014 s |
| `handshake_validity_offbyone_bug` | protocol FSM | 3 (state machine) | `assert!` | bug | bug-found | `[u8;4]`, unwind 4 | 0.010 s |
| `handshake_ordering_safe` | protocol FSM | 3 (state machine) | `assert!` | safe | verified | `[u8;4]`, unwind 4 | 0.027 s |
| `handshake_skip_bug` | protocol FSM | 3 (state machine) | `assert!` | bug | bug-found | `[u8;4]`, unwind 4 | 0.012 s |

(Rungs per the [horizon ladder](verified-systems-and-protocols.md#3-the-capability-ladder-and-where-we-stand-on-it).
The Block C protocol-FSM cases are designed in
[`protocol-state-machines.md`](protocol-state-machines.md); their bad-trace
witnesses are concrete event sequences — e.g. `handshake_skip_bug` reports
`events=[CLOSE, RECV_SYNACK, …]` (ESTABLISHED reached with no handshake).)

## Lean-cert coverage (the moat metric)

Per-case inspection of `Verdict::Verified.lean_module` (via `cert_coverage`),
printed by the `*_lean_cert_coverage` tests in each suite. The honest measured
picture for this domain:

| Suite | kernel Lean module | in-tree re-checked cert |
|---|---|---|
| network (`ic_carry_fold_equiv`, `be16_field_roundtrip`, `seq_advance_roundtrip`) | **1/3** | 3/3 |
| systems (`ring_wrapped_read_safe`, `bounded_read_safe`) | **0/2** | 2/2 |
| protocol FSM (`handshake_validity_safe`, `handshake_ordering_safe`) | **0/2** | 2/2 |
| **total safe cases** | **1/7 (14%)** | **7/7 (100%)** |

The single kernel-Lean case is `seq_advance_roundtrip` (the `u8` wrapping
add/sub modular identity) — its refutation lands in the reconstructor's covered
fragment. The checksum/header equivalences, the array+loop memory-safety proofs,
and the FSM proofs all route through **DRAT** (in-tree re-checked, but not yet a
Lean-kernel artifact). This **quantifies the cert-lane gap** for the
systems/network domain: the Lean reconstructor's fragment (UPSTREAM-FEEDBACK
U1/U4) does not yet cover bit-vector arithmetic equivalence, array/loop
refutations, or FSM invariants. Soundness is asserted (any produced module is the
real `theorem axeyum_refutation … False`), the *count* is reported, not pinned —
it rises as the reconstructor's fragment widens. This is the four-constraint
Pareto-dominance leg (3) that PLAN.md names as the structural win Z3 cannot match.

## Fuzz ↔ proof gradient (spec-as-oracle)

The *same* reference spec is exercised at both ends of the assurance dial
(`spec_oracle_gradient.rs`):

| Mode | What it does | Inputs covered | Time |
|---|---|---|---|
| cheap oracle (sampled) | fast fold vs reference spec, 200k LCG samples | sample | 0.003 s |
| cheap oracle (detect) | reference spec catches the carry-dropping impl | sample | <0.001 s |
| cheap oracle (exhaustive) | seq roundtrip over all `u8×u8` | 65 536 (all) | <0.001 s |
| **symbolic proof** | `#[verify]` `ic_carry_fold_equiv` / `seq_advance_roundtrip` | **all inputs** | 0.37 s / 2.31 s |

The cheap end is always-on and sub-millisecond; the proof generalizes the same
property to all inputs with a re-checked certificate. "Verified" is a dial, not a
one-off.

## Measured finding — the equivalence-miter + certificate perf wall

A concrete, reproducible bottleneck surfaced (demand-pull for the verify/solver
lane, **not** a soundness issue):

- The cost of a *safe* equivalence proof (UNSAT miter + evidence re-check + Lean
  attempt) grows **steeply with bit-width**: `seq_advance_roundtrip` proves in
  ~2.3 s at `u8` but did **not** finish within ~60 s at `u16`+.
- It also grows with **chained modular subtractions**: the window
  *offset-shift-invariance* lemma `(seq-start) == ((seq+d)-(start+d))` — two
  wrapping subtractions over the same `d` — did not finish within minutes even at
  `u8`, while a `Sat` bug witness over the same shape is instant. The asymmetry
  (cheap cancellation `(a+n)-n` vs. cross-cancellation `(a+d)-(b+d)`) points at
  the **bit-blast + proof-producing** route on chained modular subtraction as the
  hot spot, not the IR or the fragment. (That lemma is therefore documented but
  not committed as a live example — see the note in `network_examples.rs`.)

Bug-finding (`Sat`, one model) is fast and width-insensitive throughout; the wall
is specific to the *all-inputs* proof + certificate path.

## Rung 4 — unbounded protocol safety (`protocol_unbounded.rs`)

The handshake FSM as a `TransitionSystem` trait impl, proven for **every trace**
(not just `#[unwind(K)]`-bounded) via the solver's k-induction / PDR / certified-PDR
engines (design: [`unbounded-protocol-safety.md`](unbounded-protocol-safety.md)).
All verdicts are cross-corroborated; 5 tests green.

| Property | Engine | Result | Note |
|---|---|---|---|
| validity (`state ≤ 2`) | `prove_safety_k_induction` | **Safe** (all traces) | k-inductive |
| ordering (`ESTABLISHED ⇒ handshake`) | k-induction **and** PDR | **Safe** / **Safe** | two engines agree (the cross-check) |
| ordering, certified | `prove_safety_pdr_certified` | **Safe** + `recheck()` ✓ | 3 DRAT obligations (initiation/consecution/safety) — the first *protocol* property with an unbounded checkable proof (~16 s) |
| blind-injection bug | PDR **and** `bounded_model_check` | **Reachable** / **Reachable** | unbounded counterexample, BMC-corroborated |

**Bounded-vs-unbounded benchmark** (`bounded_vs_unbounded_validity`, single run):
bounded model checking gives a *weaker* result at each depth and its cost grows
with depth; one unbounded proof subsumes all depths — and is *cheaper* than BMC at
moderate depth.

| Approach | Result | Time | Guarantee |
|---|---|---|---|
| BMC depth 2 | `UnreachableWithinBound` | 1.9 ms | safe ≤ 2 steps (not a proof) |
| BMC depth 8 | `UnreachableWithinBound` | 12.9 ms | safe ≤ 8 steps (not a proof) |
| BMC depth 32 | `UnreachableWithinBound` | 99.9 ms | safe ≤ 32 steps (not a proof) |
| **k-induction** | **`Safe`** | **5.6 ms** | **safe for EVERY trace (a proof)** |

Honest note: I expected k-induction to be `Inconclusive` on the ordering invariant
(needing the `SYN_SENT ⇒ seen` strengthening) and PDR to fill the gap; the engine's
k-induction is stronger and closed it at `k=1`, so this example does **not** show
the k-induction-vs-PDR gap (the solver's own `tests/pdr.rs` `StuckCounter` does).
Comments were corrected to match what was measured. The unbounded certificate is
**DRAT**, not yet Lean — consistent with the 1/7 coverage above.

## Ergonomic protocol toolkit (`protocol_toolkit.rs`)

The *"natural, easy to use"* layer (design:
[`protocol-toolkit.md`](protocol-toolkit.md)). A declarative `Fsm` (states, init,
events, a transition closure, a bad-state set) compiles to a generic
`TransitionSystem`; `prove_for_all_traces` (PDR) and `find_bug` (BMC) are the
entry points. Defining + proving a protocol is **~10–12 lines** vs. the ~50-line
hand-written `TransitionSystem`. Temporal properties use state-splitting (fold the
safety automaton into the state). 11 tests green.

| Protocol (declarative) | Property | Result | Time |
|---|---|---|---|
| handshake (correct) | no `ESTABLISHED` without handshake | **Safe** (all traces, PDR) | < 5 ms |
| handshake (blind-injection bug) | — | **Reachable** (PDR + BMC + fuzz) | < 6 ms |
| **capability lifecycle** (correct) | *"a revoked capability is never used"* | **Safe** (all traces, PDR) | **8.3 ms** |
| capability lifecycle (use-after-revoke bug) | — | **Reachable** (PDR + BMC + fuzz) | **9.3 ms** |
| **two-peer handshake** (correct) | no half-open desync (joint client×server state) | **Safe** (all traces, PDR) | **29 ms** |
| two-peer handshake (desync bug) | — | **Reachable** (PDR + BMC + fuzz) | **52 ms** |

The seL4-flavored capability machine (5 states `EMPTY`/`ALLOCATED`/`GRANTED`/
`REVOKED`/`USE_AFTER_REVOKE`, 4 events) is a ~12-line `step` table; its unbounded
safety proof and its buggy-variant refutation each run in **under 10 ms**. The
headline ergonomics result: a stack author writes the state diagram and gets an
all-traces proof (or a concrete misuse trace) in milliseconds. The toolkit
re-derives the same verdicts as the hand-written rung-4 `TransitionSystem` — it
adds ergonomics, not unsoundness.

**Two-peer protocols, no toolkit change** (design:
[`fuzzing-and-multi-peer.md`](fuzzing-and-multi-peer.md)): a product of two
≤3-state peers encodes into one `BV8` state (`product = client*3 + server`), so a
*joint-state* property — "the server never reaches `ESTABLISHED` while the client
is not" (half-open desync) — is proven for all message interleavings with the
single-variable toolkit. Coupling the delivery transitions to the sender's state
(messages exist only if sent) is what makes the correct protocol safe; dropping
the ACK guard reaches the desync.

**Fuzzing ⟷ proof (the "verification *and* fuzzing" pairing):** a concrete
executor (`Fsm::reaches_bad`, independent of the symbolic encoding) fuzzes 50k
deterministic-LCG traces. On every *proven-safe* machine no trace reaches a bad
state (a soundness cross-check — DISAGREE = 0 — that also validates the toolkit's
bit-blasted encoding against direct execution); on every buggy machine fuzzing
independently finds the bad state (mirroring `Reachable`). Honest measured nuance:
for these *tiny* FSMs the symbolic proof (~4 ms) actually beats 50k fuzz traces
(~13 ms) — fuzzing's value is sub-µs single-trace latency and scaling past where
proofs time out, not batch throughput at this size.

## Verifying real Rust, not a DSL (direction A)

Closing the gap from "verify a hand-built table" to "verify actual Rust" (design +
feasibility: [`real-rust-frontend.md`](real-rust-frontend.md)). Two driverless,
no-new-deps paths landed:

| Path | What it verifies | Result |
|---|---|---|
| **Finite reflection** (`protocol_toolkit.rs`) | a real idiomatic `fn step(State,Event)->State` over `#[repr(u8)]` enums | capability lifecycle Safe for all traces; **same verdicts** as the hand-encoded `u8` version — faithful |
| **MIR-text reflection** (`mir_reflection.rs`, prototype) | the *compiled* MIR of a real function → `axeyum-ir` term | reflected term **equals the real Rust on all 256 inputs** (exhaustive cross-check) |
| **MIR + symbolic proof** (`mir_reflection.rs`) | a property of the reflected *compiled* term, for ALL inputs | `u32` lookup (2³² inputs): `lut32(x) ≤ 9` **Proved in 3 ms**; a false bound `Disproved`; `u8` eval and proof agree |

Finite reflection partial-evaluates the user's real `step` over the finite domain
(sound + complete for finite state; the same fn is run *and* proven — "two readings
of one Rust function"). The MIR prototype parses a committed `-Zunpretty=mir`
fixture (CI-robust: no rustc at test time) and proves the reflected term is exactly
the function — evidence the MIR pipeline is real. Crucially, the reflected term is
then handed to the **solver** and a property is proved *symbolically* for ALL
inputs (`axeyum_solver::prove` → `Proved`/`Disproved`): on a `u32` function this is
**3 ms** where enumerating 2³² inputs is infeasible — the payoff of
reflect-then-prove over reflect-then-enumerate. Arithmetic MIR (overflow-check
branches) is the next parser frontier; the arbitrary-Rust `stable_mir` front end is
deferred behind an ADR (it changes the dependency/trust surface).

## Next

- **Widen the Lean reconstructor to lift this domain's coverage off 1/7**: the
  measured gap is concrete — BV-arithmetic *equivalence* refutations, array/loop
  (memory-safety) refutations, and FSM-invariant refutations all route through
  DRAT today. Each is a tracked reconstructor-fragment target (UPSTREAM-FEEDBACK
  U1/U4); this scoreboard is the regression metric for that work.
- ~~**Unbounded protocol safety**~~ — **DONE** (rung 4 above): handshake validity
  and ordering proven for all traces (k-induction + PDR), with a recheckable
  certified-PDR proof and unbounded bug detection.
- **Lift the rung-4 certificate from DRAT to Lean**: the certified-PDR
  initiation/consecution/safety obligations are DRAT today — the same
  reconstructor-fragment work as the bounded cases, now for CHC obligations.
- **Richer protocol coverage**: more TCP states (simultaneous open, close
  handshake) and an **array-aware** unbounded route so buffer/window protocols
  (rung-3 today) can also be proven unbounded.
- A *generated* scoreboard (mirroring `measure_verify.rs`'s `ast::Program`
  construction) folding in these per-suite numbers automatically.
- Feed the perf-wall finding to the QF_BV word-level reduction / SAT-core lane.
