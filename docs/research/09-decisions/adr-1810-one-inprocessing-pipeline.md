# ADR-1810: One inprocessing pipeline — the shipping sequencing survives, and it moves down into `axeyum-cnf`

Status: accepted
Date: 2026-09-09
Index-summary: Closes roadmap item 1.3. Two CNF inprocessing pipelines sequence the SAME three `axeyum-cnf` passes: `axeyum_cnf::inprocess::inprocess_into` (`inprocess.rs:252`, ADR-1750, zero callers in `axeyum-solver`) and `sat_bv_backend::inprocess` (`sat_bv_backend.rs:1827-2083`, the shipping path). The inventory's framing — "the front door uses the untrusted one" — is stale by one day: ADR-1780 (2026-09-08) made the shipping path check its `unsat` against the ORIGINAL formula through `ReductionLink`, and `inprocess.rs` is the one that structurally cannot, because it has no way to express the `compact()` renumbering the backend runs. So the SEMANTICS that survives is the shipping one; the FILE that survives is `axeyum-cnf/src/inprocess.rs`, whose body is replaced by the shipping sequencing. Every ingredient the move needs — `xor_propagate`, `compact`, `ReductionLink`, and the three passes — is already in `axeyum-cnf`, so this crosses no crate boundary. What must not be lost in the move: the deadline-derived work grants and their env overrides, the `prove_unsat`-keyed recording, the per-stage telemetry `span_log` consumes, the vivify step-guard, and `inprocess.rs`'s own streaming sink — which is the route `MAX_LINKED_PROOF_STEPS` (`sat_bv_backend.rs:1179`) names as the fix for its own thin 4.06x headroom.
Index-status: accepted

## Context

Roadmap item 1.3
([`docs/solver-comparison-2026-09/11-roadmap-and-plan.md`](../../solver-comparison-2026-09/11-roadmap-and-plan.md))
asks us to decide between two CNF inprocessing implementations and delete the
loser. The inventory
([`docs/solver-inventory-2026-09/00-README.md`](../../solver-inventory-2026-09/00-README.md)
§1) describes them as "a documented, evidence-carrying implementation that
nothing calls, beside a second implementation that the shipping path actually
uses," with "a different certificate mechanism (`ReductionLink`)."

Two of the three clauses in that description are wrong, and the third is
misleading. Verified in source on 2026-09-09 at `ea8515407`.

### What is true: `inprocess.rs` has no caller in the solver

`axeyum-solver` names ten other `axeyum_cnf::` modules and never names this one.
The positive control, counted over `crates/axeyum-solver/src/`:

| `axeyum_cnf::` path | occurrences |
|---|---:|
| `check_alethe` / `check_alethe_with` | 40 |
| `proof_sat` | 14 |
| `check_drat` (all variants) | 14 |
| `check_lrat` | 8 |
| `elaborate_drat_to_lrat` (all variants) | 9 |
| `vivify_within`, `simplify`, `bve`, `tseitin_encode`, `ticks`, … | 1 each |
| **`inprocess`** | **0** |

Its callers are its own crate's tests (`crates/axeyum-cnf/tests/inprocess_proof_path.rs`),
three of its own examples (`inprocess_profile.rs`, `inprocess_pass_cost.rs`,
`inprocess_proof_check.rs`), one bench example
(`crates/axeyum-bench/examples/inprocess_ab.rs`), and two entry points in its own
crate that likewise have no solver caller — `solve_with_drat_proof_counted_inprocessed`
(`proof_sat.rs:696`) and `solve_with_drat_proof_inprocessed` (`proof_sat.rs:737`).

### What is false: "a different certificate mechanism"

`ReductionLink` is not a rival mechanism and does not live in the solver. It is
`crates/axeyum-cnf/src/reduction_link.rs:156`, exported from the same crate
(`lib.rs:142`), and ADR-1780 introduced it *specifically to close ADR-1750's own
named open item*. ADR-1750's Consequences section says it in those words:

> `sat_bv_backend` still checks its `unsat` against the reduced formula, so with
> `cnf_inprocessing` on the BVE link is trusted rather than checked. … the
> obstacle is that the backend also `compact()`s, which renumbers variables and
> breaks the correspondence between prefix and searched formula.

`inprocess.rs`'s contract is a flat `DratSink` stream, and its `InprocessOutcome`
doc states the assumption that makes it work: "Same `variable_count` as the
caller's — no pass renumbers" (`inprocess.rs:216-219`). The shipping backend
*does* renumber (`compact` at `sat_bv_backend.rs:2020`, composed into the link at
`:2029`). So `inprocess.rs` cannot express what the shipping path does, and a
proof produced by routing the shipping path through it would cover the reduced
formula rather than the caller's — the exact downgrade ADR-1780 removed.

Since ADR-1780 landed (2026-09-08), the shipping path checks through
`link.check_unsat(original, formula, &proof, MAX_LINKED_PROOF_STEPS)`
(`sat_bv_backend.rs:2812`) and returns `ProofCoverage::Original` or a
`ProofCoverage::Reduced(reason)` that names why. **The shipping implementation is
the proof-carrying one.** The inventory was written against the state of the tree
before that.

### What is misleading, and stays misleading: `inprocess.rs:138`

> "The shipping SMT path enables it by default with inprocessing
> (`SolverConfig::cnf_vivify`)."

Read to the end of the sentence this is *true*: `cnf_vivify: true` at
`backend.rs:391`, so given inprocessing, vivify is on. Read as far as a reader
normally reads, it says the shipping path runs inprocessing by default, and
`cnf_inprocessing: false` at `backend.rs:390`. Roadmap 1.2 owns the flag; this
ADR owns the sentence, and it goes with the merge.

### The duplication is orchestration, and nothing else

Both pipelines call the same three primitives from the same crate:

| step | `inprocess.rs` | `sat_bv_backend.rs` |
|---|---|---|
| subsumption | `simplify_within_recorded` (`:290`) | `simplify_within_recorded` via `run_subsume_recorded` (`:1699`) |
| vivification | `vivify_within` (`:302`) | `vivify_within` via `maybe_vivify` (`:1763`) |
| elimination | `eliminate_variables_within_recorded` (`:310`) | `eliminate_variables_within_recorded` via `run_bve_recorded` (`:1727`) |

There is no second algorithm anywhere in this pair. There are two schedulers
around one set of passes, and they differ in what each knows how to do:

| capability | `inprocess.rs` | `sat_bv_backend.rs` |
|---|---|---|
| XOR propagation before the passes, skipped under `prove_unsat` because Gaussian units are not RUP | — | `:1857-1904` |
| `compact()` + renaming composed into a checkable link | — | `:2020-2030` |
| deadline-derived, env-overridable per-pass work grants (`subsume_admission` `:1614`, `bve_admission` `:1594`) | fixed `work_budget` in the options struct | yes |
| recording keyed on `prove_unsat`, so a non-proof solve does not pay a `Vec<DratStep>` proportional to the formula | always records to the sink | `:1913` |
| per-stage timing + deadline-expiry telemetry (`subsume_ms`, `bve_ms`, `vivify_ms`, `*_deadline_expired`, `*_work_spent`) consumed by `span_log.rs:847` and `config_registry.rs` | typed `InprocessStats` only | yes |
| vivify step-guard: `check_drat(simplified, &outcome.proof).is_ok()` before accepting the pass | — | `:1781` |
| **streaming**: peak buffer is one pass's derivation, not the whole prefix | `:252` (sink, `flush` per pass) | no — the link accumulates a `Vec<DratStep>` |
| typed options surface with size admission (`max_variables`/`max_clauses`, `:177`/`:179`) | yes | untyped consts `:1145`/`:1146` |
| tests that the prefix alone verifies against the ORIGINAL formula, over six option sets | `tests/inprocess_proof_path.rs` | — |

The last three rows are the ones that make this a decision rather than a
deletion. In particular, the streaming design is not a nicety: the backend's
in-RAM ceiling is `MAX_LINKED_PROOF_STEPS = 8_000_000` (`sat_bv_backend.rs:1179`),
and its own doc records that over the 200-file `QF_BV` parity list the observed
maximum prefix was 1,971,102 steps — **4.06x of headroom, not orders of
magnitude** — and says the intended response to crossing it is "to wire the
streaming route (`ReductionLink::lifting_sink` into a `TextProofSink`) rather
than to raise the constant." ADR-1750 measured a 37.7 M-step prefix on a
3.1 M-variable instance, which is 4.7x over the cap.

## Decision

**The shipping sequencing is the one inprocessing pipeline, and it moves down
into `axeyum-cnf/src/inprocess.rs`, replacing that module's body; `fn inprocess`
and its private helpers in `sat_bv_backend.rs` are deleted and the backend
becomes a call site.**

Two halves, because "which survives" has two different answers depending on
whether you mean the behaviour or the file, and conflating them is how this kind
of merge loses something:

- **The behaviour that survives is the shipping one.** It is the superset on
  every axis that touches a verdict or a certificate — XOR propagation,
  compaction, the checkable link, deadline-derived admission, the vivify
  step-guard — and it is the one every measurement in ADR-1780 and the
  `QF_BV` parity list was taken against.
- **The file that survives is `axeyum-cnf/src/inprocess.rs`.** Pass sequencing
  over `axeyum-cnf` passes belongs in `axeyum-cnf` (ADR-0001, ADR-0006), and
  every ingredient the shipping sequencing needs is *already there*:
  `xor_propagate` (`axeyum-cnf/src/xor_propagate.rs:106`), `compact`,
  `ReductionLink`, and the three passes. The move introduces no dependency in
  either direction and lets the streaming sink, the typed option surface and the
  existing prefix-verification tests keep applying to the shipping code rather
  than to a parallel copy of it.

Concretely, `inprocess_into` grows to return a `ReductionLink` (or an outcome
carrying one) instead of writing to a bare sink, runs compaction inside, and takes
the per-pass work budgets as inputs rather than deciding them — so the
deadline-derived admission policy and the `SolveStats` telemetry stay in the
solver, where the deadline and the stats live.

`SolverConfig::cnf_inprocessing` and `cnf_vivify` remain the shipping switches
and keep their current defaults. **This ADR changes no default and no verdict.**
Flipping the default is roadmap 1.2 and is not decided here.

## Evidence

- Caller counts and the ten-module positive control, above, read from
  `crates/axeyum-solver/src/` on 2026-09-09 at `ea8515407`.
- [ADR-1750](adr-1750-a-reducing-pass-must-record-what-it-derived-not-what-it-deleted.md)
  — the pass obligation, the 37.7 M-step prefix, and the named open item that
  `compact` breaks the prefix/search correspondence.
- [ADR-1780](adr-1780-a-reduction-link-carries-the-derivation-and-the-renaming.md)
  — closes that item in the shipping backend; two mutations each kill exactly the
  two solver tests that decide an `unsat` under inprocessing and none of the other 28.
- `sat_bv_backend.rs:1179` — the measured 4.06x headroom on the in-RAM proof cap
  and its own instruction to wire streaming rather than raise the constant.
- `docs/research/03-measurements/inprocessed-unsat-proof-coverage-2026-09-08.md`
  and `inprocessing-admission-2026-09-08.md` — the parity-list coverage and
  admission measurements the shipping constants are set from.

## Alternatives

**Delete `inprocess.rs` and keep the sequencing in `sat_bv_backend.rs`.**
Rejected. It is the literal reading of the roadmap's exit criterion, and it
deletes four things that have no copy in the solver: the streaming sink (the
named fix for the proof-size ceiling), the prefix-verifies-against-the-original
test suite, the typed option surface, and the measurement rig
(`solve_with_drat_proof_inprocessed` + three examples) that produced ADR-1750's
break-even table. It also leaves `axeyum-cnf` unable to inprocess its own
formula, which is a defensible thing for a CNF crate to do for a DIMACS-in
consumer.

**Keep both and document the split.** Rejected on the repository's own rule: two
schedulers over one set of passes is exactly the shape that lets a fix land in
one and not the other. ADR-1780's compaction fix landed only in the shipping
copy, and nothing announced that the other copy was now the weaker one — which is
why the inventory recorded the relationship backwards.

**Route the shipping backend at `solve_with_drat_proof_inprocessed` as it stands.**
Rejected as unsound-in-coverage: that entry point has no notion of the
compaction the backend runs, so the resulting certificate would cover the reduced
formula. This is the alternative that looks like the cheapest merge and is the
one that silently gives up what ADR-1780 bought.

## Consequences

**What is lost if the migration is careless.** Each of these exists in exactly
one of the two copies today, so each is a thing a "keep the superset" merge can
drop without any gate noticing:

1. **The deadline-derived work grants** (`subsume_admission` `:1614`,
   `bve_admission` `:1594`, `admit_occurrence_pass`) and their env overrides
   `AXEYUM_SUBSUME_BUDGET_MULTIPLE` / `AXEYUM_BVE_BUDGET_MULTIPLE`. These are
   measured constants with `const {assert!}` invariants at `sat_bv_backend.rs:4012`
   and `:4146`. `InprocessOptions` carries a *fixed* `work_budget` instead. If the
   merged path takes the options-struct form, admission silently changes and the
   parity numbers move for a reason nobody will attribute correctly.
2. **`recording = config.prove_unsat`** (`:1913`). `inprocess_into` always writes
   to the sink. On a non-proof solve the shipping path pays nothing for the
   prefix; a merged path that always records pays a `Vec<DratStep>` proportional
   to the *formula* on every solve — ADR-1750 measured that at 37.7 M steps.
3. **The vivify step-guard** at `:1781`. `inprocess_into` accepts vivify's proof
   unexamined.
4. **Per-stage telemetry.** `span_log.rs:847` reads `cnf_inprocess`;
   `config_registry.rs` documents individual keys. `InprocessStats` is a typed
   struct with different fields. Both surfaces have consumers; the merge owes
   both.
5. **`InprocessOptions::preprocess()` has `vivify: false`** (`inprocess.rs:142-150`)
   while the shipping default is `cnf_vivify: true` (`backend.rs:391`). If the
   backend starts naming an `InprocessOptions` arm, the arm must be built from
   `SolverConfig` field by field, not chosen by name, or the default behaviour
   changes silently.
6. **Streaming**, if the merge takes the `ReductionLink`'s in-RAM `Vec` shape
   wholesale. Keeping `inprocess.rs` as the surviving file is what makes it
   natural to keep; it is not automatic.

**What becomes easier.** One place to add a pass (roadmap 2.1's SCC /
equivalent-literal substitution, and Phase 3.2's remaining passes) instead of
two. One place for the 1.5 tick valve to gate. `axeyum-cnf`'s existing
prefix-verification tests start covering the shipping code instead of a parallel
copy.

**What becomes harder.** `axeyum-cnf::inprocess` grows from a 485-line module with
one clean contract into the crate's scheduling surface, and it acquires a
`ReductionLink` in its return type — so a caller who only wants a flat DRAT stream
now goes through an object with a `coverage` notion. That is the price of having
one of these instead of two.

**Revisit when** in-search inprocessing lands (ADR-1750's first open item), which
changes the shape from "a pre-pass with a prefix" to "a schedule interleaved with
search," and will want the valve from roadmap 1.5 in the same place.

## Migration

Roadmap item 1.3. Ordered so the tree is green and the certificate story is
unchanged at every step:

1. Extend `axeyum-cnf::inprocess` so `inprocess_into` accepts per-pass work
   budgets (`Option<u64>` each, as `run_subsume`/`run_bve` already take) and an
   `Option<&mut ReductionLink>` in place of the bare sink, keeping the current
   sink signature as a thin wrapper so `proof_sat.rs:696`/`:737` and the three
   examples do not change. No solver change; the existing `inprocess_proof_path`
   suite must still pass unmodified.
2. Move XOR propagation and `compact` + `link.rename` into it, behind explicit
   options (`xor_propagate: bool`, `compact: bool`), defaulting off so step 1's
   callers are bit-identical.
3. Replace the body of `sat_bv_backend::inprocess` (`:1827-2083`) with a call,
   keeping `maybe_inprocess` (`:1221`), the admission constants (`:1145`/`:1146`),
   the grant helpers, and every `stats.backend.push` where they are. Delete
   `run_subsume`, `run_subsume_recorded`, `run_bve`, `run_bve_recorded`, and
   `maybe_vivify`'s pass call — but keep `maybe_vivify`'s `check_drat` step-guard,
   moving it into the module as an option.
4. Correct `inprocess.rs:138-140` to say what is actually true: inprocessing is
   default-off (`backend.rs:390`); `cnf_vivify` is default-on and is a no-op
   without it.
5. Then, and separately, roadmap 1.2 decides the default.

**Exit criterion.** The roadmap's own wording — "One implementation remains; the
other's file is gone" — is the wrong shape for this pair, because the sequencing
is being moved rather than deleted and no file disappears. The falsifiable
replacement, mechanically checkable:

> `crates/axeyum-solver/src/sat_bv_backend.rs` contains **zero** calls to
> `simplify_within_recorded`, `simplify_with_options`, `vivify_within`,
> `eliminate_variables_within`, `eliminate_variables_within_recorded`, `compact`
> and `xor_propagate` — the seven names that constitute pass sequencing — and its
> `axeyum_cnf::` import list no longer names them. The solver's inprocessed
> `unsat` on the 200-file `QF_BV` parity list still reports
> `ProofCoverage::Original` on every one of the 117 `unsat` files it did before
> the merge, with the same verdicts on all 200.

The negative control that must exist before this is believed: re-run ADR-1780's
two mutations (corrupt one derived clause; drop the renaming) against the merged
path and require that each still kills exactly the two solver tests that decide
an `unsat` under inprocessing, and none of the other 28. A merge that moves the
code without moving the mutation kills has not been shown to preserve anything.

## What would falsify this decision

- **`axeyum-cnf` cannot host the sequencing without reaching upward.** If any
  part of the shipping schedule turns out to need `SolverConfig`, `SolveStats`,
  `Instant`-derived solver deadlines, or `axeyum-bv` — anything the crate cannot
  see — then the boundary is in the wrong place, the sequencing belongs in the
  solver, and `inprocess.rs` should be deleted down to its option/stats types and
  its test suite instead. (Checked and not the case today for the seven names
  above; `xor_propagate`, `compact` and `ReductionLink` are all in `axeyum-cnf`.)
- **Proof coverage regresses.** If the merged path reports
  `ProofCoverage::Reduced` on any parity-list file that reported `Original`
  before, the merge lost the thing ADR-1780 bought and must be reverted rather
  than patched.
- **The mutations stop killing.** If either ADR-1780 mutation kills a different
  number of tests after the merge, the certificate is no longer wired the way the
  measurement assumed.
- **A verdict moves.** Any change in the `:status` sweep or the `QF_BV` parity
  verdicts falsifies the claim that this is a refactor.
