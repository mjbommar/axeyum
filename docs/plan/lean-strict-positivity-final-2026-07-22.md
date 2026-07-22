# Lean strict positivity: M4 final result and handoff

Status: complete; ADR-0352 accepted; TL2.11 and T6.0.2 DONE

Date: 2026-07-22

Decision: [accepted ADR-0352](../research/09-decisions/adr-0352-preregister-lean-strict-positivity.md)

Prior checkpoints:

- [M0 source freeze](lean-strict-positivity-m0-2026-07-22.md);
- [M1 trusted preflight](lean-strict-positivity-m1-2026-07-22.md);
- [M2 public matrix and generated grammar](lean-strict-positivity-m2-2026-07-22.md);
- [M3 official/import boundary](lean-strict-positivity-m3-2026-07-22.md).

## Final result

Axeyum now enforces pinned Lean 4.30's strict-positivity rule for every
non-parameter constructor field in its currently representable single-family
inductive profile. The trusted preflight runs before provisional environment
insertion and distinguishes:

- a family occurrence in a `Pi` domain as
  `NonPositiveInductiveOccurrence`;
- a containing term that is not the exact fixed-parameter, complete-arity,
  occurrence-free-index family application as `InvalidInductiveOccurrence`.

Both failures carry the family, constructor, and zero-based field index and
leave the ordered environment unchanged. Direct recursive families continue to
admit and compute. Positive recursive-indexed and reflexive/higher-order fields
pass positivity but retain their explicit feature declines; no inductive
admission was widened in TL2.11.

## Accepted evidence

All ADR-0352 exit gates are met:

1. the exact Lean commit, rule, cases, resources, and stop conditions were
   committed and pushed before implementation;
2. a tested precedence case proves the positivity traversal finishes before
   provisional family insertion or constructor type inference;
3. the two stable error variants carry exact constructor/field identity;
4. direct-recursive `Nat`, `List`, and tree admission/computation remain green;
5. positive recursive-indexed and reflexive fields retain their respective
   later feature declines;
6. all registered negative/invalid public rows reject transactionally;
7. a fixed-seed 840-case public grammar repeats byte-identically with a frozen
   summary across all profiles, both sorts, and depths zero through four;
8. eight bounded exact-Lean observations and the mandatory CI differential
   agree with the registered positive/negative source population;
9. a synthetic importer mutation propagates the typed error without
   publication, while the immutable official construct matrix remains
   unchanged;
10. the complete focused Rust, official-Lean, Python, parity, foundational,
    documentation, and link gates pass.

The official/wire distinction remains explicit: rejected declarations cannot
be exported by official Lean, so the importer propagation case is synthetic
format evidence, not official-wire evidence.

## Final bounded gates

The final acceptance pass used at most two Rust build jobs, the 4 GiB
wrapper/cgroup, one Lean worker, exact pinned Lean 4.30, and temporary linker
output under ignored `target/`:

| gate | result |
|---|---|
| `cargo test -p axeyum-lean-kernel` with `AXEYUM_REQUIRE_LEAN=1` | 182 unit + 38 integration + 1 doctest passed |
| strict-positivity grammar | 840 unique cases twice; frozen bytes reproduced |
| strict-positivity official differential | 4 sources x 2; 2 accepts, 6 diagnostic rejects |
| `cargo test -p axeyum-lean-import` | 30 integration + 1 compile-fail doctest passed |
| focused kernel/import clippy | all targets, warnings denied, passed |
| focused kernel/import rustdoc | warnings denied, passed |
| focused rustfmt | six milestone-owned Rust files passed |
| M0 + M3 observation validators | 14 Python tests passed |
| foundational resources | 137 concept rows and 174 packs validated |
| parity validators | DISAGREE=0; all generated/check-only artifacts current |
| documentation links | all links passed |
| `git diff --check` | passed |

The earlier `/tmp` LLD bus error is environmental and reproducibly disappears
when the exact doctest/rustdoc commands place temporary linker files under
`target/`; the final acceptance pass uses that explicit path and is green.

## Scope and non-claims

This completes strict positivity only for the single-family API Axeyum exposes
today. It does not claim:

- recursive-indexed or reflexive recursor/IH support;
- mutual-group positivity (TL2.13 must widen the occurrence set atomically);
- frontend lowering for nested or well-founded definitions;
- unsafe-inductive support;
- full Lean kernel, `Init`/`Std`/mathlib, or ecosystem compatibility.

## Handoff

The primary semantic path is now TL2.12: implement recursive-indexed and
reflexive/higher-order fields as one induction-hypothesis generalization,
because both require hypotheses of the form
`Pi telescope, motive (recursive-field args)`. Reuse the immutable
`MiniVector` and `MiniAcc` official streams and keep the direct-recursive,
non-positive, generated-grammar, importer-publication, and construct-matrix
controls mandatory.

TL2.12 must be preregistered before changing admission. TL2.13 mutual groups
remain blocked on TL2.12 and must generalize positivity from one family name to
the complete mutual occurrence set in the same admission change.
