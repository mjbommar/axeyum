# Consumer applications

Axeyum has three user-facing verification applications built on the same typed
IR, solver, model-replay, and evidence layers as the SMT-LIB path. This page is
their current documentation front door. The dated research and per-application
plans below are design records; project-wide priority and live work remain in
the root [PLAN.md](../../PLAN.md).

## What exists today

| Application | Current surface | Measured construction-known corpus | Start here |
|---|---|---:|---|
| Bounded-property SDK | Typed Bool/BV/Int properties returning `Proved`, `Disproved(counterexample)`, or `Unknown` | 16 cases: 5 proved, 11 disproved, 0 unknown | [`axeyum-property`](../../crates/axeyum-property/README.md) · [scoreboard](property/SCOREBOARD.md) |
| EVM bug-hunter | Runtime-bytecode symbolic execution returning replayed findings, `SafeUpToBound`, or `Unknown` | 18 cases: 13 bugs, 5 safe, 0 unknown | [`axeyum-evm`](../../crates/axeyum-evm/README.md) · [scoreboard](evm/SCOREBOARD.md) |
| Bounded Rust verifier | `#[axeyum::verify]` over a restricted Rust surface, returning a reproduced counterexample, bounded `Verified`, or `Unknown` | 14 cases: 7 bugs, 7 verified, 0 unknown | [`axeyum-verify`](../../crates/axeyum-verify/README.md) · [scoreboard](verify/SCOREBOARD.md) |

The [aggregate scoreboard](SCOREBOARD.md) therefore records **48 cases, 31
bugs/disproofs, 17 safe/proved results, 0 unknown, and 0 disagreements**. These
are construction-known capability cases plus independent cross-checks, not a
head-to-head decide-rate measurement against every named competitor.

## Result and trust boundaries

The applications share a result discipline, but they do not all establish the
same claim:

- A property proof uses Axeyum's replay-checked evidence path. A standalone Lean
  module is best effort and only present when reconstruction covers the proof.
- An EVM finding is reported only when its calldata witness reproduces in the
  separate concrete interpreter. `SafeUpToBound` excludes the modeled bug
  classes only within the configured path/step bounds. Its re-checked solver
  `EvidenceReport` is optional, and the EVM crate does not currently reconstruct
  that safety claim to Lean.
- A Rust counterexample is re-run against the original function under
  `catch_unwind`. `Verified` covers the supported language fragment and stated
  unwind bound; it is not an unbounded proof of arbitrary Rust. Certificate and
  Lean-module availability are explicit, and the warm loop route is currently
  decision-only.
- Unsupported constructs, unresolved behavior, or exhausted resources remain
  `Unknown`. They are not silently converted into a safe or proved result.

The committed differential fuzzers for EVM and Rust verification exercise the
wrong-safe boundary. The per-application scoreboards and crate READMEs describe
the exact corpus, oracle, proof coverage, and remaining limits.

## Run or regenerate the measured examples

Preview the property artifacts without writing a tracked file:

```sh
cargo run -p axeyum-property --example property_corpus_scoreboard -- markdown
cargo run -p axeyum-property --example property_corpus_scoreboard -- json
```

Regenerate its committed artifacts by supplying the output paths:

```sh
cargo run -p axeyum-property --example property_corpus_scoreboard -- \
  markdown docs/consumer-track/property/SCOREBOARD.md
cargo run -p axeyum-property --example property_corpus_scoreboard -- \
  json docs/consumer-track/property/corpus.json
```

The EVM and verifier measurement examples always rewrite their committed
scoreboard and JSON artifact. Run them only when you intend to review those
changes:

```sh
cargo run -p axeyum-evm --example measure_evm
cargo run -p axeyum-verify --example measure_verify
```

See the complete [Cargo example catalog](../reference/examples.md) before
running generators or maintainer diagnostics.

## Honest open limits

- The hevm/halmos/Kani competitor scoreboards remain install-gated. The current
  corpus totals do not substitute for those future comparisons.
- The generic scalar QF_BV browser path exists, but `axeyum-evm` does not yet
  expose an EVM-specific JavaScript/WASM binding.
- Lean reconstruction coverage is partial, and the verifier's warm loop route
  currently returns a decision without a packaged certificate.
- Both program frontends are bounded and intentionally incomplete: unsupported
  EVM behavior and Rust constructs return `Unknown`.

## Design and evidence records

- [`01-ideas-and-ranking.md`](01-ideas-and-ranking.md) — initial application
  candidates and ranking (dated 2026-06-25).
- [`02-research-synthesis.md`](02-research-synthesis.md) — source-grounded SOTA
  and Axeyum API research from the selection phase.
- [`03-decision.md`](03-decision.md) — selected applications and original build
  sequence.
- [`SCOREBOARD.md`](SCOREBOARD.md) — current aggregate measurement and soundness
  qualifications.
- [`UPSTREAM-FEEDBACK.md`](UPSTREAM-FEEDBACK.md) — consumer-discovered solver
  gaps and their reconciliation status.
- [`property/`](property/) · [`evm/`](evm/) · [`verify/`](verify/) — committed
  scoreboards, machine-readable corpora, and historical implementation journals.
