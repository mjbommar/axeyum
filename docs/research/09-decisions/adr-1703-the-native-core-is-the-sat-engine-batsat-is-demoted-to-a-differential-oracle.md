# ADR-1703: The Native CDCL Core Is The SAT Engine; BatSat Is Demoted To A Differential Oracle

Status: accepted
Index-summary: Native CDCL core is the SAT engine on every path; BatSat demoted to a non-default `batsat-reference` oracle
Date: 2026-09-05

## Context

[ADR-0007](adr-0007-first-pure-rust-sat-adapter.md) chose `rustsat-batsat` as
the **first** pure-Rust SAT adapter. It was chosen in June 2026, before any
native core existed, and its own text labels it scaffolding: "`unsat` results
from this adapter are explicitly lower-assurance until a proof-producing path
and checker exist", and "Phase 6 still owns the custom CDCL implementation.
This ADR chooses the adapter baseline to beat or replace."

That proof-producing path now exists.
[ADR-0011](adr-0011-drat-unsat-proof-checking.md) added the trusted DRAT
checker, [ADR-0012](adr-0012-proof-producing-sat-core.md) added the native
core, and
[ADR-0613](adr-0613-unsat-is-certified-by-following-hints-not-by-searching-for-them.md)
added the LRAT route. The native core in
[`crates/axeyum-cnf/src/proof_sat.rs`](../../../crates/axeyum-cnf/src/proof_sat.rs)
is no longer the "intentionally minimal and slow" reference ADR-0012
described. The
[2026-09-05 SAT/SMT review](../11-design-review/2026-09-05-sat-smt-performance-and-architecture-review.md)
§3.1 measured it as "a credible modern design: a flat clause arena with
per-clause headers, blocking-literal watch lists, VSIDS with geometric decay
and rescale, phase saving plus target rephasing, Luby and EMA-glue restarts
with Glucose-style blocking, LBD glue tiers, and `reduce_db`."

ADR-0012 nevertheless left BatSat the default "until the benchmarking gate says
otherwise", and that gate was never run. The measured consequence, §3.2 D1 of
the same review: three Boolean search engines coexist, the modern one "sits
unused on the proof path", and `SolverConfig::native_cdcl` still defaults to
`false` (`crates/axeyum-solver/src/backend.rs:382`), so `SatBvBackend` calls
BatSat unless a caller opts in.

The structural reason the default could not simply be flipped: the native core
had **no incremental interface**. `proof_sat.rs` exposed only one-shot
`solve_with_drat_proof*` entry points, while the warm path — `IncrementalSat`
and `IncrementalCnf` (ADR-0009), consumed by the LIA DPLL(T) driver
(`dpll_lia.rs`), the warm BV engine (`incremental.rs`) and `axeyum-bench` —
was BatSat-only.

## Decision

**The native CDCL core is the SAT engine on every Axeyum path. BatSat is
demoted to the role ADR-0002 gives Z3: a non-default, feature-gated
differential oracle, scheduled for removal.**

Concretely:

1. The native core gains a persistent, assumption-capable interface
   (`NativeIncrementalCdcl` in `proof_sat::incremental`): clauses added between
   solves, `solve_assuming`, retained learned clauses and heuristic state, a
   failed-assumption core readout, and the same deadline/conflict-budget
   plumbing as the one-shot API. DRAT emission is **optional** and off on the
   warm path; with it off the search trajectory is unchanged, because the sink
   is output-only (the property already asserted for the one-shot core).
2. `IncrementalSat` and `IncrementalCnf` are re-implemented over that object
   with their public surface unchanged.
3. `SatBvBackend`'s primary SAT search is the native core unconditionally.
   `SolverConfig::native_cdcl` becomes a no-op retained for API compatibility
   and is documented as deprecated. The CDCL(XOR) fallback (ADR-0035) triggers
   on an `unknown` from the native core exactly as it previously did on an
   `unknown` from BatSat.
4. `batsat`, `rustsat`, and `rustsat-batsat` become **optional** dependencies
   of `axeyum-cnf` behind a non-default feature `batsat-reference`. The default
   dependency graph contains none of the three, verified by
   `cargo tree -e normal -p axeyum-cnf`. `RustSatBatsatSolver`,
   `solve_with_rustsat_batsat*`, `BatSatDeterminism` and
   `rustsat_batsat_determinism` compile only under that feature.
5. The only sanctioned use of the feature is differential testing:
   `crates/axeyum-cnf/tests/native_vs_batsat_differential.rs` runs both engines
   over the committed micro-CNF corpus and a seeded random 3-SAT family at the
   threshold ratio and asserts verdict agreement plus model validity. Like every
   feature-gated suite in this repository it compiles to **zero tests** without
   its feature and exits 0; its header says so and the gate must confirm a
   nonzero count.
6. **Slice 2** removes the feature, the dependencies, and the ~70 historical
   documentation references. This ADR does not do that sweep.

Call sites that only wanted "a SAT verdict" (tests and examples in
`axeyum-cnf`, `axeyum-search`, `axeyum-bench`) move to a native equivalent with
the same `SatResult` shape: `solve_with_native_core`,
`solve_with_native_core_timeout`, `solve_with_native_core_limits`, and
`NativeCdclSolver: SatSolver`. Sites that are genuinely differential keep
BatSat and move behind `batsat-reference`.

## Evidence

- ADR-0007 §Consequences already scheduled this: "the adapter baseline to beat
  or replace", with UNSAT "capability-marked lower assurance".
- ADR-0012 §Decision: BatSat is "the fast default solving path ... until the
  benchmarking gate says otherwise"; §Consequences leaves "when it replaces the
  adapter as the default" as future work. That decision point is what this ADR
  closes.
- 2026-09-05 review §3.1 (native core is a credible modern design) and §3.2 D1
  (the table of three engines; "the modern core sits unused on the proof path").
- The benchmarking methodology's gate (a) — does SAT time dominate? — reads
  **true** on the public `20190311-bv-term-small-rw-Noetzli` slice at ~0.95 SAT
  share over 1,416 decided `sat-bv` instances.
- **Gate (b) has now been run**, for the first time since ADR-0012 deferred to
  it in June 2026:
  [2026-09-05 gate (b) measured](../11-design-review/2026-09-05-gate-b-sat-core-measured.md),
  artifact [`bench-results/sat-core-gate-b-20260905/`](../../../bench-results/sat-core-gate-b-20260905/README.md).
  Four engines on byte-identical Axeyum-generated DIMACS, 20 s per instance,
  `taskset -c 0-7`, one engine at a time:

  | Family | Files | BatSat | native | CaDiCaL | Kissat |
  |---|---:|---:|---:|---:|---:|
  | p4dfa (exhaustive) | 113 | 4 | **6** | 10 | 11 |
  | Noetzli (100-file seeded sample) | 100 | 86 | **86** | 88 | 89 |

  PAR-2 (s): p4dfa 38.729 / 38.107 / 37.203 / 36.941; Noetzli 5.604 / 5.605 /
  5.247 / 4.613. **Zero cross-engine sat/unsat disagreements and zero invalid
  SAT models** across all 852 (engine, file) pairs.

  The finding this ADR rests on: **the native core is never worse than BatSat
  and sometimes better** — six decided against four on p4dfa, tied on the
  Noetzli sample, never a worse PAR-2. There is no measured case for BatSat as
  the stronger in-tree engine. Two honest qualifications, from the note itself:
  the gap to CaDiCaL/Kissat is real but *modest and family-dependent*, so gate
  (b) does not by itself argue for jumping the core-tuning queue; and the host
  carried heavy uncontrolled load throughout, so the engine *ordering* is more
  reliable than the absolute seconds. Neither qualification touches this
  decision, because gate (b) asks *how much to invest in tuning the core*, not
  *which core we own* — and it cannot be satisfied by keeping a third-party
  engine on the default path.

### What this changes about assurance

This is the substantive part, and it is not a performance claim.

Today the trust ledger carries a boundary: an `unsat` from the BatSat adapter
is `SatProofStatus::Unchecked` and can never be anything else, because the
adapter emits no proof. `axeyum-cnf`'s own crate docs state it: "The `BatSat`
adapter's proofless UNSAT is lower assurance." Every default-path QF_BV `unsat`
sits on the wrong side of that line unless a caller sets `prove_unsat`.

With the native core on every path, that boundary **disappears rather than
moves**: every `unsat` the engine produces is derived by learning RUP clauses
and ends in the empty clause, so a DRAT proof is available *by construction* for
the asking, checkable by `check_drat` (ADR-0011) or, with hints, by the linear
`check_lrat` (ADR-0613). "Proofless UNSAT" stops being a category of result
Axeyum can produce and becomes a per-call choice not to spend the proof-checking
time. `sat` is unaffected: it was, and remains, checked by replaying the lifted
model against the original terms.

Two honest caveats, recorded rather than smoothed over:

- Emission is **off by default on the warm path**, for speed. So a warm `unsat`
  is still stamped `Unchecked` unless proof emission is requested. The
  difference from BatSat is that the capability exists at all; with BatSat it
  did not.
- An `unsat` **under assumptions** does not derive the empty clause, so it
  carries a failed-assumption core rather than a refutation proof. That is
  inherent to assumption-based solving, not a property of this engine.

### Performance

The owner's decision does not rest on the native core being faster. A slower
native core would be a to-do for our engine, not a reason to keep BatSat. As it
happens the gate (b) measurement above found the native core at least BatSat's
equal on both public families, so the flip costs no measured capability — but
that is a convenience, not the argument. The before/after measurement for this
lane is recorded in
[`docs/plan/status/1703-native-core-retire-batsat.md`](../../plan/status/1703-native-core-retire-batsat.md)
and any regression is reported there and here as a finding, never tuned away or
hidden.

## Alternatives

- **Keep BatSat as the default until the native core wins a benchmark.** This
  is the ADR-0012 status quo and it has held for nearly three months without
  the gate being run. It also inverts the identity commitment: ADR-0002 makes
  the ground-up stack the product and the third-party engine the scaffolding,
  so "our engine ships when it is fastest" is the wrong ordering. Rejected.
- **Keep both engines as a runtime portfolio.** Rejected as the identity creep
  ADR-0002 already names. Two default engines means two soundness surfaces, two
  determinism stories, and — as §3.2 D1 measured — the better one going unused.
- **Delete BatSat now, in one slice.** Rejected: BatSat is the independent
  referee for the native core's verdicts, and ADR-0002's own argument for
  keeping Z3 as an oracle applies verbatim. Removing the referee in the same
  change that promotes the thing it refereed is the wrong order.
- **Give the native core a fake incremental interface** (rebuild the solver per
  solve, retaining nothing). Rejected: `IncrementalSat`'s callers — the LIA
  DPLL(T) driver in particular — solve repeatedly over a growing database, and
  a solver that discards learned clauses between calls is incremental in name
  only.

## Consequences

- Easier: one Boolean search engine to profile, tune, and prove things about;
  every default-path `unsat` is proof-capable; the default dependency graph
  loses three crates; `axeyum-cnf` builds for `wasm32` with no adapter
  indirection.
- Harder: the native core now carries the whole load, including corpora BatSat
  was tuned for. Any capability regression the frontier ratchet reports is a
  real finding against our engine and is recorded, not hidden.
- Revisited: slice 2 removes `batsat-reference`, its dependencies and the
  historical documentation references. ADR-0007 is not superseded — its
  *choice* (BatSat as the first adapter) was correct and served its purpose;
  this ADR retires the role.
