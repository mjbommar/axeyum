# ADR-0335: Preregister Tock log2 proof and scoreboard

Status: accepted
Date: 2026-07-21

## Context

ADR-0334 closes authenticated local T5.5.2 capture/parser admission for Tock's
two public integer-logarithm helpers. The accepted two-root build emits one
raw-identical LLVM module, and LLVM 22 extraction plus Axeyum's checked parser
admit both canonical scalar functions. No property query has run.

The target-selection note already freezes the property family: zero behavior,
equivalence to an independent floor-log specification, and the most-significant
set-bit characterization, with replayed wrong-index, inverted-zero-arm, and
corrupted-high-partition controls. T5.5.3 must now measure exactly that family
without treating capture admission, a fixture-shaped proof, or a solver verdict
without replay/checking as target credit.

## Decision

Create one local-only, zero-row Tock proof producer over the exact authenticated
canonical files. It must reflect those files directly, prove the preregistered
properties with checked `unsat` evidence, replay every SAT control against both
the reflected target and an independent native source oracle, and atomically
emit a measured scoreboard.

## Frozen inputs

1. Pin committed capture summary SHA-256
   `29e01e9eac94cd718d347150762da7234394d062ecbfbf71f1f405cc0e76ba01`,
   local capture result SHA-256
   `96a987b1cbb8d84fa200001f56b3d2be068359ef8bbc7ec6c261814a4cba3aa9`,
   stable capture identity `9ec0a0c3...84b9`, Tock commit/tree, module hash
   `f9a1e155...c76fd`, and cache inventory/active-resolution identities.
2. Pin and read only the ignored canonical files:
   `log_base_two.ll`, 331 bytes, SHA-256 `5063d99b...d51c`; and
   `log_base_two_u64.ll`, 374 bytes, SHA-256 `f8e23452...a4e3`. Require their
   widths/instruction counts to match capture metadata. No source, module,
   symbol, expected proof verdict, witness, or timing may be substituted.
3. Build the runner from an archive of the exact pushed Axeyum `HEAD`, not the
   dirty working tree. Pin the registration's producer/test files plus the HEAD
   bytes of `Cargo.lock` (`004d1441...d552`), root `Cargo.toml`
   (`edc82766...ba61`), and `axeyum-verify/Cargo.toml`
   (`3720953e...10ec`). Use the registered nightly Cargo/rustc identities from
   capture v3, `--locked --offline`, one job, and an ignored fresh target/output.

## Frozen obligations

For each input width `W` in `{32, 64}`, bind one `BVW` symbol directly to the
authenticated reflected function and prove four separate goals:

1. **defined** — the complete returned value is defined for every input,
   including the selected-arm treatment of `ctlz(0, true)` poison;
2. **zero** — definedness and `result(0) = 0`;
3. **floor-log equivalence** — definedness and equality to an independent
   threshold/staged-bit-search term built only from existing BV constants,
   unsigned comparisons, extracts, Boolean connectives, and `ite`; and
4. **MSB characterization** — definedness and, for every nonzero input, the
   selected result bit is one while every higher bit is zero.

The 64-bit target compares its explicit narrowed `i32` result. The independent
specification must not call `ctlz`, `leading_zeros`, the reflected result, or
the target oracle.

## Solver, evidence, and controls

1. Run every proof with the pure-Rust QF_BV backend, `prove_unsat=true`, a
   30-second per-query timeout, 5,000,000 deterministic resource units,
   2,048 MiB solver memory, 250,000 term nodes, 1,000,000 CNF variables, and
   5,000,000 CNF clauses. Disable preprocessing/inprocessing/vivification/lazy/
   XOR/native-CDCL policy toggles explicitly so the measured route is the direct
   eager baseline. The outer producer retains one Cargo job and the standing
   2.5 GiB high / 4 GiB hard / 512 MiB swap cgroup.
2. A proof row receives credit only for `ProofOutcome::Proved` whose provenance
   records the exact limits and `prove_unsat=true`, whose returned evidence was
   rechecked by `prove`, and whose per-result trust ledger contains no
   uncertified step. Record backend, evidence family, certified steps, term
   count, and wall time. `Unknown`, timeout, limit exhaustion, bare `unsat`, or
   any uncertified step receives no proof credit and closes this v1 result.
3. Require six `Disproved` controls: for each width, textually alter the
   compiler's `31`/`63` XOR index constant; invert the exact zero-select arms;
   and corrupt the independent top-bit partition. Do not weaken definedness to
   manufacture a witness.
4. Extract every countermodel input, replay the correct reflected term and
   mutated term/spec with `axeyum-ir::eval`, and require the correct result to
   equal a separately executed native source oracle:
   `0 -> 0`, otherwise Rust's width-matched integer `ilog2`. The mutated result
   must differ. Record witness/input/results and `replay=pass`; any missing,
   ill-typed, non-discriminating, or oracle-disagreeing model is a soundness
   failure, not a refutation.

## Result and atomicity gates

1. The exact official Cargo command is one ignored integration test with
   `--exact --nocapture --test-threads=1`; structured rows are parsed by a
   hash-pinned Python producer. No other test may contribute target credit.
2. The scoreboard has exactly two functions, eight property rows, and six
   controls. Success requires `PROVED=8`, `REFUTED_REPLAYED=6`, `UNKNOWN=0`,
   `DISAGREE=0`, capture/parser admission retained, and exact per-query plus
   total wall/RSS accounting. Counts are results only after all gates pass.
3. Stable result identity includes all frozen inputs, runner/source hashes,
   solver configuration, proof/control rows and witnesses, evidence/trust
   families, and scoreboard counts; it excludes only wall/RSS/cgroup-event
   observations. Recompute identity before commit.
4. Write only beneath ignored `target/tock-log2-20260721/proof-v1` through a
   sibling partial directory and rename after every check. Commit only Axeyum
   producer/test/registration, compact result metadata, and prose. Tock LLVM,
   build products, and proof scratch remain ignored local bytes.
5. Commit and push this zero-row ADR before adding the producer/test/registration.
   Commit and push that complete checkpoint before the single official query
   invocation. Failure closes proof v1; no limit, obligation, oracle, replay,
   or evidence gate may be weakened after observation.

## Result

Proposed. The ignored Rust integration runner now implements the eight frozen
goals, six exact mutations, fully certified evidence/provenance gate, and
reflected-plus-native witness replay. The Python producer validates the capture,
canonicals, tools, pushed-HEAD archive, exact solver/command/resource policy,
structured row set, stable identity, and atomic output. Its compact registration
pins three producer files, three HEAD source manifests, four tools, both
canonical hashes, and capture identity `9ec0a0c3...84b9`.

Five focused producer tests pass, including malformed trust/replay rows,
identity projection, archive traversal, and atomic cleanup. The non-authenticated
independent-spec Rust test, strict target Clippy, and the full `axeyum-verify`
package test/doctest suite pass under the capped one-job environment; the suite
reports the authenticated scoreboard test as ignored. Commit and push this
checkpoint before its single official invocation. No target property query,
proof, countermodel, replay, scoreboard row, or measured T5.5.3 result exists.

Pushed checkpoint `7c3960c9` then passes local/tracking/remote identity and
registration/capture validation, but its pre-query HEAD materialization stops
because Python's safe tar filter rejects the repository's sole Git symlink,
`corpus/public`, whose committed target is absolute. The proof workspace does
not consume `corpus/`. The corrected zero-row producer now requires the archive
link set to equal exactly `[corpus/public]`, skips every link byte, and still
requires all registered producer/build inputs to extract as regular hash-matched
files. A focused test retains traversal rejection and proves that this one
explicit link is omitted. Commit/push the correction before repeating archive
preflight. No Cargo command or target query started; proof v1 remains unobserved.

Correction `8d059285` is pushed and byte-identical at local HEAD, its tracking
ref, and remote `main`. The repeated pre-query validation accepts the capture
and registration, authenticates the pushed commit/tree, and safely materializes
the archive with exactly `corpus/public` omitted. Every registered regular input
is present and hash-matched. This successful gate ran no Cargo command or target
query; proof v1 remains unobserved and is authorized for one official invocation.

## Result

Accepted as a negative v1 result. Runner commit `10605313` was pushed and
matched local HEAD, its tracking ref, and remote `main` before the single
official invocation. Registration, capture, canonical functions, tools, source
hashes, and archived-HEAD materialization all validate. Cargo then exits before
compilation because the committed archived `Cargo.lock` cannot represent the
selected package graph under the frozen `--locked --offline` command:

```text
stage=runner
kind=cargo_test
detail=error: cannot update the lock file .../source/Cargo.lock because --locked was passed to prevent this
```

Zero compilations, property queries, proofs, controls, or scoreboard rows run.
Atomic cleanup leaves no output or partial directory, and the resource guard
reports no OOM-delta failure. Exact negative metadata is committed in
`bench-results/verify-tock-log2-20260721/proof-v1-negative.json`.

Proof v1 ends here and must not be rerun. A successor may correct only the
locked source snapshot: resolve and commit a workspace lockfile that matches the
already frozen manifests, then preregister its exact hash and a new output path.
It must preserve the authenticated canonical bytes, eight proofs, six controls,
solver/resource policy, pushed-HEAD isolation, and every replay/trust gate.

## Rejected alternatives

- **Credit ADR-0327's fixture-shaped proofs.** Rejected: they validate the
  semantic extension but do not consume authenticated target bytes.
- **Use `leading_zeros` as the proof specification.** Rejected: it is the same
  semantic idea as `ctlz`; the staged BV specification must be independent.
- **Accept default bare `unsat`.** Rejected: this target is the concrete checked
  proof use case requested by the reviewer track.
- **Replay only the model against the mutation.** Rejected: the correct
  reflection and independent native oracle must also agree at every witness.
- **Run from the dirty workspace.** Rejected: unrelated user changes must not
  enter the measured artifact.
- **Combine broader Tock functions or performance comparisons.** Rejected:
  this result measures only the two preregistered helpers and is not a speed
  headline.
