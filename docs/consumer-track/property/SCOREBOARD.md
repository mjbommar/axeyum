# axeyum-property SCOREBOARD

> **Auto-generated. Do not edit by hand.**
> Regenerate with `cargo run -p axeyum-property --example property_corpus_scoreboard -- markdown docs/consumer-track/property/SCOREBOARD.md`.

Last updated: 2026-06-27.

This is the committed graduated SDK corpus gate for
`axeyum-property`. It is not yet a broad external-vs-SOTA benchmark; it is the
app-level honesty gate that prevents SDK claims from living only in ad hoc unit
tests. External proptest/Kani-style comparison remains the next PROP.6 step.

## Commands

```sh
CARGO_BUILD_JOBS=2 cargo test -p axeyum-property --test corpus -j1 -- --nocapture
cargo run -p axeyum-property --example property_corpus_scoreboard -- json docs/consumer-track/property/corpus.json
cargo run -p axeyum-property --example property_corpus_scoreboard -- markdown docs/consumer-track/property/SCOREBOARD.md
```

Machine-readable artifact: [`corpus.json`](corpus.json).

## Summary

| metric | value |
|---|---:|
| corpus cases | 8 |
| proved | 2 |
| disproved | 6 |
| unknown | 0 |
| mismatches / DISAGREE | 0 |
| Lean-required cases | 1 |
| Lean-required available | 1 |

## Cases

| id | tier | workflow | expected | checks | baseline analogue |
|---|---|---|---|---|---|
| `sdk-bv-reflexive-proof` | P0 | certificate success over fixed-width BV | proved | checked evidence kind starts with `unsat-`; assertion count is stable; standalone Lean module is available | z3.rs/Kani assertion proof |
| `sdk-int-assumption-proof` | P1 | integer implication under an SDK assumption | proved | checked evidence is present through `ProofCertificate::summary()` | Kani precondition/assertion proof |
| `sdk-u8-minimized-counterexample` | P0 | unsigned small failing input | disproved | minimized `u8` witness is `6`; Rust scalar replay binding renders deterministically | proptest-style shrinking |
| `sdk-i8-signed-minimized-counterexample` | P1 | signed fixed-width input order | disproved | minimized signed witness is `-3`; two's-complement Rust binding preserves signed intent | Kani/proptest signed integer witness |
| `sdk-aggregate-counterexample-render` | P1 | struct-shaped symbolic input | disproved | minimized transfer witness is `{ enabled: false, amount: 1, balance: 0 }`; direct Rust aggregate initializer renders | Kani struct harness / proptest `Arbitrary` struct |
| `sdk-u8-uadd-overflow-helper-witness` | P1 | unsigned overflow helper witness | disproved | minimized `u8` overflow witness is `(x = 1, y = 255)`; replay bindings render deterministically | Kani arithmetic-overflow check / Rust verifier overflow assertion |
| `sdk-derived-struct-counterexample-lift` | P1 | `derive(Symbolic)` struct witness | disproved | derived `TransferInput` lifts to `{ enabled: false, amount: 1, balance: 0 }`; aggregate initializer renders | Kani struct harness / proptest `Arbitrary` struct |
| `sdk-explicit-nested-aggregate-replay` | P1 | caller-owned nested aggregate replay | disproved | generated multi-case fixture file includes caller-owned imports, nested `transfer.limits` setup, `TransferInput` setup, and a helper-rendered `Result<bool, _>` replay assertion in order | Rust verifier domain replay body / Kani nested harness struct |

## Next Gates

1. Add a baseline runner that compares the same property shapes against
   proptest-style random/shrunk witnesses and Kani-style bounded assertions.
2. Broaden the corpus across BV widths, overflow predicates, nested aggregates,
   assumptions, and certificate fragments.
3. Keep `corpus.json` and this scoreboard generated from the shared corpus
   module instead of hand-edited.
