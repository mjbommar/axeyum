# Lane `sos-fallback` — the SOS fallback minted axioms under the honest route's name

<!-- plan-section: lane-status -->

**Topic 3: the reconstruction fallback must not mint axioms under the honest
route's name.** ADR-[1673](../../research/09-decisions/adr-1673-a-weaker-route-may-not-render-under-the-strong-routes-identifier.md).

## Status

Landed. The SOS route's `UnsupportedTerm` fallback no longer renders under
`axeyum_refutation`; which name a module gets is derived from
`Kernel::axiom_footprint`, and the attested name is not a substring of the
honest one. Four tests in `reconstruct::sos_fallback_labelling_tests`, three of
them adversarial, with a four-mutant table.

**Not landed: the frequency census.** How often the fallback fires across the
committed corpora is unmeasured. One slice completed
(`corpus/public-curated/synthetic/QF_NRA`: 10 SOS queries, 0 fallbacks, with a
forced-fallback positive control reporting 10 of 10); the `corpus/public-curated`
run (exit 124 at 900 s) and the whole-`corpus/` run (exit 143 at 3000 s)
each produced zero lines of output. Because
of that, the question of deleting the fallback outright is left open in the ADR
rather than decided. A follow-up lane should give the probe a per-file deadline.

## What changed

| File | Change |
| --- | --- |
| `crates/axeyum-solver/src/reconstruct.rs` | `LEAN_MODULE_ATTESTED_THEOREM`, `ctx_refutation_axiom_footprint`, `render_ctx_module_named_by_footprint`, the wrapper split into `sos_certificate_attestation_module`, and the `sos_fallback_labelling_tests` module |
| `docs/research/09-decisions/adr-1673-*.md` | new |
| `docs/research/09-decisions/README.md` | regenerated (`gen-adr-index.py`) |
| `docs/plan/status/sos-fallback-2026-09-06.md` | this file |

No other crate was touched. `crates/axeyum-cas`, `lean/` and
`docs/math-department/` were not touched.

## The finding, in one line

The wrapper is a hand-inlined copy of
`direct::reconstruct_checked_structural_certificate_to_lean_module` **minus its
banner**, which is why the two guards that exist for exactly this
(`gate_module_content` and `prove_unsat_to_lean_theory_module`) both passed it:
they classify by a marker the emitter forgot to apply.

## Mutation table

Every row RUN, `cargo test -p axeyum-solver --features full --lib
sos_fallback_labelling_tests` (4 tests).

| Mutant | Predicted | Ran | Verdict |
| --- | --- | --- | --- |
| MA — `render_ctx_module_named_by_footprint` ignores the footprint and always renders the honest name | 1 dies: `..._does_not_wear_the_honest_routes_name` | 3 passed / 1 failed, exactly that test | as predicted |
| MB — attested name becomes `axeyum_refutation_attested` (a substring of the honest one) | 2 die: `assert_names_are_not_substrings...` + `..._does_not_wear...` | 2 passed / 2 failed, exactly those | as predicted |
| MC — distinct name kept, structural-attestation banner dropped | 1 dies: `..._does_not_wear...` (its `is_structural_attestation` half) | 3 passed / 1 failed, exactly that test | as predicted |
| MD — mint the opaque proposition under a `hyp._n` name so `minted_axioms_of` returns empty | 2 die; the guard falls through to the honest name | 3 passed / 1 failed — only the fixture's *anchor* died; the guard did **not** fall through | **prediction wrong**, see below |

Plus one reachability control, not a guard mutant: forcing `reconstruct_sos_proof`
to return `UnsupportedTerm` turns the probe's
`corpus/public-curated/synthetic/QF_NRA` reading from `fallback=0` to
`fallback=10`.

### What MD taught

`minted_axioms_of` is **calibrated for the LRA naming scheme**.
`is_query_local` recognizes a query's own assumption as
`axeyum.reconstruct.<route>.hyp._<n>` — it needs that route segment.
`ReconstructCtx::fresh_name` emits `axeyum.reconstruct.hyp._<n>` with no route,
so every `ReconstructCtx`-built refutation reports a non-empty minted set,
honest `QF_BV` and `QF_UF` reconstructions included. MD could not defeat the
guard, and the reason is that the guard is coarser than intended rather than
finer.

Two consequences, both recorded in the ADR and in the helper's doc comment:

- `render_ctx_module_named_by_footprint` is **scoped to the SOS attestation**.
  Reaching for it from another `ReconstructCtx` route without recalibrating
  `is_query_local` would rename a module that has earned the honest name.
- What MD *did* kill was the fixture's anchor, which grepped the rendered module
  for an `axeyum.reconstruct.prop.` line — a name assertion inside a test whose
  point is that names are not the authority. The wrapper is now split
  (`sos_certificate_attestation_module`) so the minted footprint is returned
  beside the module and the fixture asserts on the `Vec`.

## Gates

| Gate | Count | Exit |
| --- | --- | --- |
| `cargo test -p axeyum-solver --features full --lib -- --test-threads=4` | **1464 passed**, 0 failed | 0 |
| `cargo test -p axeyum-solver --features full --lib sos_fallback_labelling_tests` | **4 passed**, 0 failed, 233 s | 0 |
| `cargo test -p axeyum-solver --features full --test corpus_regression` | **1 passed**, 0 failed | 0 |
| `cargo clippy -p axeyum-solver --all-targets --features full -- -D warnings` | — | 0 |
| `cargo check --workspace --all-targets` | — | 0 |
| `cargo fmt --all --check` | — | 0 |
| `./scripts/check-links.sh` | "all links ok" | 0 |
| `python3 scripts/gen-adr-index.py` | rows=884, 1673 not duplicated | 0 |

The bare `--lib` sweep without `--test-threads` was killed at the
`cargo-serialized` memory ceiling (exit 143) twice before the capped run
succeeded; that is the ceiling firing, not a failure.

Not run: the z3 differential fuzzes (no arithmetic touched), the frontier
ratchet, `just check` / `check.sh`, and the real-`lean` cross-check.

## Consumer audit

| Consumer | Keys on | Was it conflating? |
| --- | --- | --- |
| `prove_unsat_to_lean_theory_module` (`reconstruct.rs`) | `STRUCTURAL_ATTESTATION_MARKER` via `of_module_source` | **Yes** — returned the shim as a theory module. Fixed: it now declines. |
| `gate_module_content` (`reconstruct.rs`) | the same marker vs the fragment table | **Yes** — agreed with `Sos`'s declared class. Fixed: now `ModuleContentMismatch`. |
| `evidence.rs::produce_nra_sos_evidence` / `check_sos_evidence` | `reconstruct_sos_to_lean_module(...).ok()` into `Evidence::UnsatSos::lean_module`, no content gate | **Yes.** The field's doc says "when `lean_module` is present, the refutation is ALSO backed by a kernel-checked Lean proof"; for a fallback query that was false. Now at least self-declaring (banner + attested name). Carrying the content class on `Evidence::UnsatSos`, or storing `None`, is the real fix and belongs to that file's owner. **Not touched — out of this lane's scope.** |
| `axeyum-bench/examples/probe_selected_evidence_lean.rs:159` | `module.contains("theorem axeyum_refutation")` | Not today — it renders its own module rather than consuming the SOS route. The bare-substring pattern is why the attested name is not a suffix. **Not touched — another session owns `axeyum-bench`.** |
| `tests/lean_crosscheck.rs::assert_structural_shape` | `source.contains("theorem axeyum_refutation")` | Not today; SOS attestations are not in its population. Same substring pattern. |
| `tests/lean_crosscheck.rs` family/module ratchets | `LeanModuleContent::of_module_source` | Would have counted a fallback module as theory content. No corpus row takes the fallback in the measured slice, so no ratchet moves. |
| `tests/evidence.rs::qf_nra_sos_certificate_wrapper_carries_lean_module`, `lean_crosscheck.rs::qf_nra_sos_certificate_audit_rows_check_in_real_lean` | named for the wrapper | **Stale names.** Both fixtures (`nra-sos-unsat-k01`, `nra-sos-strict-unsat-d01`) take the **honest** route today, measured. They do not exercise the wrapper and have not for some time. |
