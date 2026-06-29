# Verified systems & protocols — a horizon note for `axeyum-verify`

> **Status:** research / design note (2026-06-29). Forward-looking. It does **not**
> change the shipped positioning of `axeyum-verify` (a pure-Rust, certifying,
> *bounded* panic-safety verifier with no annotation burden, positioned against
> Kani — see [`PLAN.md`](PLAN.md) and [`STATUS.md`](STATUS.md)). It works
> *backwards* from an ambitious application domain — **systems and network-protocol
> code, in the spirit of seL4** — to a concrete, prioritized backlog that the
> existing `#[axeyum::verify]` surface can start delivering on **today**, and names
> the rungs above it.

## 1. The end goal (work backwards from here)

> *Could `Rust + axeyum` become a natural, low-ceremony way to build a new OS or
> network stack whose safety- and correctness-critical core carries machine-checkable
> evidence — the seL4 promise, but pure-Rust, certificate-bearing, and without a
> separate proof language?*

seL4 is the existence proof that "entire spec → verified implementation" is
achievable for serious systems software — at ~20 person-years and a ~20:1
proof-to-code ratio, in Isabelle, against a hand-written C kernel. The cost is
dominated by *human-guided proof in a language that is not the implementation
language* (the **two-language problem**). The bet this note explores is the one
the whole project rests on — **untrusted fast search, trusted small checking** —
applied to systems code: let the programmer write **fast Rust**, reflect it into
the IR, discharge the safety/correctness obligations the decidable core can reach
**automatically**, and hand back a **certificate a small independent checker (and
ultimately the Lean kernel) accepts**. Where automation can't reach, fail
honestly rather than `sorry`.

We will not reach seL4 parity, and we should never claim it. The useful question
is the *gradient*: which rungs of a verified-systems ladder are reachable now,
which are the next bounded increments, and which are genuinely multi-month.

## 2. Why systems & protocol code is the right target for *this* stack

Most of a wire protocol and a microkernel's hot path is **bit-vectors and bounded
arrays** — fixed-width header fields, modular counters, length/offset arithmetic,
checksums, ring buffers, capability tables, page-table index math. That is exactly
`axeyum-verify`'s shipped fragment (`uN/iN/bool`, bitwise/arith incl.
`wrapping_*`/`%`, fixed `[T; N]` + indexing, `if`/`match`, `assert!`/`assert_eq!`,
`#[unwind(K)]`-bounded loops) and the solver's strongest theory (QF_BV / QF_ABV
with a checkable-evidence path). The match is not a coincidence — it is the reason
to push *this* domain first.

Two alignments make it especially natural:

- **Rust's machine integers *are* bit-vectors.** `u32` wraparound mod 2³² and the
  total-function edges are the same semantics axeyum models verbatim per SMT-LIB
  totality. A pure bounded function over machine ints + arrays is not *approximated*
  by an IR term; it *is* one. (`lower.rs` already emits an explicit `divisor == 0`
  bad state precisely because BV `/`,`%` are SMT-LIB-total.)
- **The borrow checker is the tractability win.** Aliasing is controlled at the type
  level, so the bounded-pure fragment we can reflect today is exactly the fragment
  where reasoning is decidable — no separation-logic machinery required *yet*.

## 3. The capability ladder, and where we stand on it

| Rung | Property class | Reachable today via `#[verify]`? | Mechanism |
|---|---|---|---|
| 0 | **Panic/UB-freedom** (overflow, ÷0, OOB, `unwrap`-None, `assert!`) | **Yes — shipped** | `verify_program` ORs bad states, proves `¬OR` |
| 1 | **Spec/impl equivalence** (a fast impl equals a reference spec) | **Yes — *expressible now*** | `assert_eq!(fast(x), spec(x))` inside a `#[verify]` fn ⇒ a reachable-mismatch query; `unsat` = bounded equivalence proof |
| 2 | **Functional postconditions** (output satisfies a predicate) | **Yes — *expressible now*** | inline `assert!(post(inputs, out))` |
| 3 | **Bounded protocol/state-machine safety** (k steps, invariant holds) | **Partial** | `#[unwind(K)]` loops / warm `bounded_model_check` over scalar+BV state (`bmc.rs`, `loop_system.rs`) |
| 4 | **Unbounded safety** (inductive invariant, all traces) | **No (engine exists, not wired to `#[verify]`)** | CHC/PDR — [ADR-0048](../../research/09-decisions/adr-0048-chc-pdr-verify-guarded-invariant-discovery.md), gated on interpolation ([ADR-0047](../../research/09-decisions/adr-0047-craig-interpolation-proof-based.md)) |
| 5 | **Relational / hyperproperties** (non-interference, constant-time) | **No** | self-composition over the equivalence pattern (rung 1) — a research item |
| 6 | **Whole-module / self-hosting** (verify a real `axeyum-bv` leaf fn; MIR coverage) | **No** | `stable-mir-json` consumer — Phase 3, [`PLAN.md`](PLAN.md) |

**The headline finding for the backlog:** rungs **1 and 2 are reachable on the
shipped surface with zero new macro features** — equivalence and postconditions are
just `assert_eq!`/`assert!`, and the project has not yet *demonstrated* this in the
systems domain. That is the cheapest, highest-signal next increment, and it
directly exercises the "two readings of one Rust function" idea: the impl and the
spec are both ordinary Rust, reflected by the same front end, reconciled by one
solver call that emits a certificate.

## 4. Worked target list (the seL4-flavored beachhead)

Each item is a small, in-fragment Rust function carrying its own `#[verify]`
verdict (safe ⇒ asserts `Verified`; buggy ⇒ `#[verify(expect_bug)]` asserts a
reproducing witness). Ordered by ROI; the first block needs **no new capability**.

**Block A — rungs 1–2, no new macro features (do first):**
1. **Internet checksum fold equivalence** (RFC 1071). Two ways to compute the
   16-bit ones-complement end-around-carry fold of a 32-bit accumulator must be
   bit-equal: `assert_eq!`. `unsat` = a bounded equivalence proof with a Lean-eligible
   certificate. The canonical "untrusted fast fold, trusted small check" demo.
2. **Packet header field extraction** with bounds — extract/concat over a small
   byte array; a *safe* masked accessor verifies, a *buggy* one (wrong shift/mask)
   exposes a witness.
3. **TCP sequence-number window test** under mod-2³² wraparound — the classic
   defect class. A `wrapping_*`-based predicate verifies its intended cyclic
   property; a signed-comparison variant yields a wraparound counterexample.

**Block B — rung 3, bounded loops/arrays (next):**
4. **Length-guarded buffer copy** (a Heartbleed-shaped check) — a copy bounded by
   an attacker-controlled length field over a fixed `[u8; N]`: guarded ⇒ verifies,
   unguarded ⇒ OOB witness.
5. **Ring-buffer index arithmetic** (`(head + 1) % CAP`) — an seL4-IPC-flavored
   bounded queue: indices stay in range; an off-by-one variant is caught.

**Block C — rungs 4–6 (named, not yet built):**
6. Wire a bounded protocol **state machine** (e.g. a handshake) through warm BMC;
   later lift to **unbounded** safety via the CHC/PDR engine (rung 4).
7. **Constant-time / non-interference** of a comparison via self-composition of the
   rung-1 equivalence pattern (rung 5).
8. **Self-hosting**: verify one real `axeyum-bv` leaf function (rung 6, Phase 3).

## 5. The fuzz↔proof gradient (spec-as-oracle)

`axeyum-verify` already has the *soundness floor*: a reported counterexample is
re-run through the original function and must actually panic (`reproduce.rs`,
`panics_on`) — DISAGREE = 0. The systems backlog should lean on the same idea as a
**cost gradient**: the reference spec used in a rung-1 `assert_eq!` is *also* a
cheap differential oracle. Before paying for the full bounded-equivalence proof,
the spec can be exercised against the impl by ordinary `proptest`/concrete
execution (already a dev-dependency in `axeyum-property`); the proof is the
high-assurance end of a dial whose cheap end is always on. This makes "verified"
an affordable habit rather than a heroic one-off — the property that decides
whether teams write specs at all.

## 6. References (design touchstones, not yet cited in-repo)

- **seL4** — full functional correctness of an OS kernel (Isabelle); the cost
  baseline and the existence proof.
- **Verus, Creusot, Kani/CBMC** — the contrast set already named in
  [`PLAN.md`](PLAN.md): axeyum's differentiators are *no annotation burden* +
  *single-stack kernel-checkable certificate*. (In-repo reference clone:
  `references/CreuSAT`, a Creusot-verified Rust SAT solver.)
- **Aeneas / Charon, `stable-mir-json`** — the MIR-subset reflection path for the
  Phase-3 coverage upgrade (rung 6); not the start.
- **Protocol landmarks** — TCP/IP in HOL4 (Bishop/Norrish/Sewell, validated against
  real traces), TLS 1.3 (Tamarin/ProVerif feeding the IETF design; miTLS/Low*) —
  evidence that near-complete protocol formalization is real, at a cost.

## 7. Honest limits

- Everything in Blocks A–B is a **bounded** guarantee (fixed widths, `#[unwind(K)]`).
  "Verified" here means *no bad state reachable within the bound* — not total
  correctness. This must be stated wherever results are reported, exactly as the
  shipped scoreboard already does.
- Equivalence/postconditions via `assert_eq!`/`assert!` inherit the fragment's
  limits (no heap, traits, closures, floats; scalar+fixed-array state). Real
  network/OS code leaves the fragment quickly; the value is in the
  correctness-critical *cores*, not whole modules — until rung 6.
- The unbounded story (rung 4) is the CHC/PDR engine, itself gated behind
  interpolation and MBP. Do not promise it from the `#[verify]` surface yet.

## 8. Next increment (this lane)

Land **Block A** as new `tests/*_examples.rs` in `axeyum-verify` (consumer of the
shipped macro — no macro-internals changes), demonstrating rung-1 equivalence and
rung-2 postconditions in the systems/network domain, each carrying its `#[verify]`
verdict. Then **Block B**. Measure on a small systems scoreboard slice
(decided / DISAGREE = 0 / Lean-cert coverage), mirroring the existing
[`SCOREBOARD.md`](SCOREBOARD.md) discipline. Keep all guarantees labeled *bounded*.

**Landed (2026-06-29):** Blocks A+B committed as `tests/network_examples.rs` and
`tests/systems_examples.rs`; the fuzz↔proof gradient as
`tests/spec_oracle_gradient.rs`; **Block C** (bounded protocol state machines,
designed in [`protocol-state-machines.md`](protocol-state-machines.md)) as
`tests/protocol_fsm_examples.rs`. Measured results, gradient timings, the
equivalence-miter perf-wall finding, and **Lean-cert coverage (the moat
metric)** are in
[`verified-systems-and-protocols-scoreboard.md`](verified-systems-and-protocols-scoreboard.md):
**13 `#[verify]` cases, 7 verified / 6 bug-found, DISAGREE = 0**; coverage
**1/7 (14%) kernel-Lean, 7/7 in-tree-certified** — quantifying the cert-lane
gap (BV-equivalence, array/loop, and FSM refutations route through DRAT today).
The first FSM safety properties verified include *"ESTABLISHED requires a
handshake"* (a blind-injection class caught as a one-event bad trace).

**Rung 4 (unbounded) also landed** as `tests/protocol_unbounded.rs` (design:
[`unbounded-protocol-safety.md`](unbounded-protocol-safety.md)): the handshake
FSM as a `TransitionSystem`, proven for **every trace** — validity and ordering
`Safe` via both k-induction and PDR (independent engines agreeing), a
**certified-PDR** proof whose three DRAT obligations re-check (the first protocol
property with an unbounded checkable proof), and the blind-injection bug caught as
an unbounded `Reachable` counterexample. A benchmark shows one unbounded proof
(5.6 ms) subsumes — and beats — bounded model checking at depth 32 (99.9 ms, still
not a proof).

**Ergonomics — the *"natural, easy to use"* layer also landed** as
`tests/protocol_toolkit.rs` (design:
[`protocol-toolkit.md`](protocol-toolkit.md)): a declarative `Fsm` (states,
init, events, a transition closure, a bad-state set) compiles to a generic
`TransitionSystem` with `prove_for_all_traces` / `find_bug` entry points, so
defining + proving a protocol is **~10–12 lines** instead of ~50 of hand-written
arena boilerplate (temporal properties via state-splitting). An seL4-flavored
**capability lifecycle** — *"a revoked capability is never used"* — is proven for
all traces in **8.3 ms** (and its use-after-revoke bug refuted in 9.3 ms), the
whole protocol a ~12-line table. The toolkit re-derives the same verdicts as the
hand-written `TransitionSystem` — ergonomics, not unsoundness.

The remaining rungs are **lifting the rung-4 certificate from DRAT to Lean**,
**widening the Lean reconstructor** to lift coverage off 1/7, and an
**array-aware** unbounded route for buffer/window protocols.
