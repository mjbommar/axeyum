# axeyum-property SCOREBOARD

Last updated: 2026-06-27.

This is the first committed graduated SDK corpus gate for
`axeyum-property`. It is not yet a broad external-vs-SOTA benchmark; it is the
app-level honesty gate that prevents SDK claims from living only in ad hoc unit
tests. External proptest/Kani-style comparison remains the next PROP.6 step.

## Command

```sh
CARGO_BUILD_JOBS=2 cargo test -p axeyum-property --test corpus -j1 -- --nocapture
```

## Summary

| metric | value |
|---|---:|
| corpus cases | 5 |
| proved | 2 |
| disproved | 3 |
| unknown | 0 |
| mismatches / DISAGREE | 0 |
| Lean-required cases | 1 |
| Lean-required available | 1 |

## Cases

| id | tier | workflow | expected | checks | baseline analogue |
|---|---|---|---|---|---|
| `sdk-bv-reflexive-proof` | P0 | certificate success over fixed-width BV | Proved | checked evidence kind starts with `unsat-`; assertion count is stable; standalone Lean module is available | z3.rs/Kani assertion proof |
| `sdk-int-assumption-proof` | P1 | integer implication under an SDK assumption | Proved | checked evidence is present through `ProofCertificate::summary()` | Kani precondition/assertion proof |
| `sdk-u8-minimized-counterexample` | P0 | unsigned small failing input | Disproved | minimized `u8` witness is `6`; Rust scalar replay binding renders deterministically | proptest-style shrinking |
| `sdk-i8-signed-minimized-counterexample` | P1 | signed fixed-width input order | Disproved | minimized signed witness is `-3`; two's-complement Rust binding preserves signed intent | Kani/proptest signed integer witness |
| `sdk-aggregate-counterexample-render` | P1 | struct-shaped symbolic input | Disproved | minimized transfer witness is `{ enabled: false, amount: 1, balance: 0 }`; direct Rust aggregate initializer renders | Kani struct harness / proptest `Arbitrary` struct |

## Next Gates

1. Add a baseline runner that compares the same property shapes against
   proptest-style random/shrunk witnesses and Kani-style bounded assertions.
2. Broaden the corpus across BV widths, overflow predicates, nested aggregates,
   assumptions, and certificate fragments.
3. Emit machine-readable JSON so app scoreboards can be regenerated rather than
   hand-edited.
