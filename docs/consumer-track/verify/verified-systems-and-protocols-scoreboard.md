# Verified systems & protocols — measured scoreboard

Companion to [`verified-systems-and-protocols.md`](verified-systems-and-protocols.md).
Measured from the committed example suites driving the real `#[axeyum::verify]`
macro:

- `crates/axeyum-verify/tests/network_examples.rs` (Block A)
- `crates/axeyum-verify/tests/systems_examples.rs` (Block B)
- `crates/axeyum-verify/tests/spec_oracle_gradient.rs` (the fuzz↔proof gradient)

Reproduce: `cargo test -p axeyum-verify --test network_examples --test
systems_examples --test spec_oracle_gradient -- -Z unstable-options
--report-time` (nightly for per-test times). Times are a single indicative
wall-clock run (debug build, `scripts/mem-run.sh`), 2026-06-29; not tuned.

## Headline

- **9 `#[verify]` cases**: 5 safe → **verified**, 4 buggy → **bug-found**.
- **DISAGREE = 0** (soundness floor): every safe case proves within its bound;
  every bug witness is re-run through the *original* fn and actually panics
  (`reproduce::panics_on`).
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

(Rungs per the [horizon ladder](verified-systems-and-protocols.md#3-the-capability-ladder-and-where-we-stand-on-it).
A *Lean-cert coverage* column is deferred: it needs per-case inspection of
`Verdict::Verified.lean_module`, the headline-moat metric the existing
[`SCOREBOARD.md`](SCOREBOARD.md) reports — a follow-up for a generated harness.)

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

## Next

- A *generated* scoreboard (mirroring `measure_verify.rs`'s `ast::Program`
  construction) that also records per-case Lean-cert coverage.
- Block C rungs: bounded protocol state machine → unbounded via CHC/PDR
  ([ADR-0048](../../research/09-decisions/adr-0048-chc-pdr-verify-guarded-invariant-discovery.md)).
- Feed the perf-wall finding to the QF_BV word-level reduction / SAT-core lane.
