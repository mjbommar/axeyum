# ADR-1701: The theory interface gains final check, a driver-owned propagation queue, lazy explanation and dynamic atom registration; the CDCL(T) search moves onto the native clause arena

Status: accepted
Index-summary: `TheorySolver` gains `final_check` / `propagate_into` / `explain` / `take_new_atoms`, all defaulted; `CdclT`'s own Boolean search is scheduled onto the native `proof_sat` arena (slice 2)
Index-status: accepted (slice 1 landed 2026-09-05; slice 2 scoped, not implemented)
Date: 2026-09-05

## Context

The [2026-09-05 SAT/SMT performance and architecture
review](../11-design-review/2026-09-05-sat-smt-performance-and-architecture-review.md)
§3.2 records two adjacent debts that together account for the divisions where
this solver is weakest.

**D2 — the online theory interface is too thin for an efficient CDCL(T).**
`pub trait TheorySolver` (`crates/axeyum-solver/src/euf_egraph.rs`) has four
methods and nothing else:

```rust
fn assert(&mut self, atom: usize, value: bool) -> Result<(), Vec<TheoryLit>>;
fn push(&mut self);
fn pop(&mut self);
fn propagate(&self) -> Vec<TheoryProp>;
```

Four consequences, each of them measured or documented in the tree:

1. **No final check.** A theory cannot separate a cheap partial check, run on
   every `assert`, from a complete check run once at a total Boolean
   assignment. `lra_online.rs`'s own module header says `assert` "re-decid[es]
   feasibility on the **warm general simplex** … on every call" — the opposite
   of the Dutertre–de Moura design that engine implements, in which an assert
   moves a bound and the expensive `check` is deferred.
2. **No driver-owned propagation queue.** `propagate(&self)` returns a freshly
   allocated `Vec<TheoryProp>` per call, so every propagation fixpoint
   iteration allocates, and the theory has no way to record what it has
   already emitted.
3. **No lazy explanation.** Every propagation carries its full
   `reason: Vec<TheoryLit>`, materialised at propagation time. Most propagated
   literals never appear in a conflict analysis, so most of that work — for
   LRA a Farkas extraction, for difference logic a cycle walk — is discarded.
4. **Dynamic atom registration is not in the trait.** `cdclt.rs` notes that
   "dynamic theory variables may follow Tseitin auxiliaries" and the alignment
   is maintained by side tables in the driver, driven from outside by each
   adapter's own final-check refinement loop.

**D1 — three Boolean search engines, and the weakest carries the weakest
divisions.** `CdclT` (`cdclt.rs`) stores clauses as `clauses: Vec<Vec<Lit>>`
and unit-propagates by scanning the whole database per fixpoint pass: no clause
arena, no watch lists, no blocking literals. The native core
(`axeyum-cnf/src/proof_sat.rs`), which
[ADR-1703](adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md)
just made *the* SAT engine, has all three. Measured the same day on the
identical PHP(7,6) CNF
([microbenchmarks-2026-09-05.md](../08-planning/microbenchmarks-2026-09-05.md)):
`CdclT::solve` **39.6 ms**, the native core **5.7 ms** — about **7x**. Every
route named in the linear-arithmetic diagnosis runs on the slower one.

**Why now.** The [2026-08-21 linear-arithmetic deficit
diagnosis](../05-algorithms/linear-arithmetic-deficit-diagnosis-2026-08-21.md)
§4 Cause A found `dl-online` returning "budget exhausted in the online
difference-logic driver" on **64 of 65** traced QF_IDL misses and **51 of 55**
traced QF_RDL misses, and §2 split the QF_LRA misses between the 1,024-atom
admission cap (29) and slow CDCL(T) search (36). Those are not four
independent problems; they are the D2 interface and the D1 engine seen from
the corpus side. Recommendation 4 of the review names exactly this work and
calls it "the Track 1 P1.5 keystone the roadmap already names".

## Decision

**The `TheorySolver` trait gains four capabilities — a final check, a
driver-owned propagation queue, lazy explanation, and dynamic atom
registration — every one of them with a default implementation, so the ten
production implementors compile unchanged and any theory that does not opt in
behaves byte-identically. Separately, and as a second slice, `CdclT`'s
hand-rolled Boolean search is to be replaced by the native `proof_sat` clause
arena and watch scheme.**

### Slice 1 — the interface (this ADR's implemented half)

Four new trait methods, each defaulted:

```rust
/// A complete check at a total Boolean assignment. Default: `Sat` — a theory
/// that decides everything on `assert` needs no second opinion.
fn final_check(&mut self) -> FinalCheckOutcome { FinalCheckOutcome::Sat }

/// Sound propagation into a driver-owned queue. Default: drains `propagate`
/// into the queue, so an unmodified theory is unchanged.
fn propagate_into(&mut self, queue: &mut PropagationQueue) { … }

/// Resolves a deferred explanation handle. Default: `None` — a theory that
/// never emits a handle can never be asked to resolve one.
fn explain(&mut self, handle: ExplanationId) -> Option<Vec<TheoryLit>> { None }

/// Number of theory atoms registered since the last call; the driver appends
/// and activates one SAT variable per atom. Default: `0`.
fn take_new_atoms(&mut self) -> usize { 0 }
```

with three new public types:

- `FinalCheckOutcome` — `Sat`, `Conflict(TheoryExplanation)`, or `Unknown`.
  `Unknown` is a first-class answer (a budget or an overflow inside the
  complete check), and the driver degrades the whole search to
  `Outcome::Unknown` on it. It is never a verdict.
- `TheoryExplanation` — `Eager(Vec<TheoryLit>)` or `Lazy(ExplanationId)`.
- `PropagationQueue` — a reusable `Vec<(TheoryLit, TheoryExplanation)>` the
  driver owns, clears between fixpoint iterations and keeps the capacity of.

**Where laziness is offered, and where it is not.** A handle is only useful
where the driver *defers* consuming a reason. That is true of a propagation
reason (most propagated literals are never resolved against) and of a
final-check conflict (which the driver may resolve after a backjump). It is
**not** true of an `assert` conflict, which the driver learns from in the same
step it receives it; offering a handle there would add a resolution point and
save nothing. `assert` therefore keeps its eager `Vec<TheoryLit>` signature,
which is also why the ten implementors need no edit.

**Soundness rules that come with the handles.**

- A handle is valid exactly while the literal it explains is assigned. The
  driver drops every deferred handle in `backjump_to`, at the same moment it
  pops the theory, so a handle can never outlive the theory state that
  justifies it.
- An unresolvable handle (`explain` returns `None`) is a **theory bug, not a
  verdict**. The driver abandons the search and returns `Outcome::Unknown`.
  It never treats a missing explanation as an empty clause, which would be a
  wrong `unsat`.
- A `final_check` conflict is not required to name a current-decision-level
  literal, so the driver cannot hand it straight to 1-UIP analysis (which
  assumes the trigger-literal invariant and would underflow its path counter).
  Before analysing a final-check conflict the driver backjumps to the highest
  decision level named in the core; an all-level-0 core then yields the empty
  asserting clause, which is the correct `Unsat`.

### Slice 1 — the two opt-ins

`DlTheory` (`dl_online.rs`) and `LraTheory` (`lra_online.rs`), the two theories
the linear-arithmetic diagnosis names, opt in:

- **LRA** moves to the Dutertre–de Moura split its own engine was built for.
  `assert` now does bound bookkeeping plus a **cheap** consistency check —
  the simplex `check` runs on assert only while the asserted system is small
  enough that it is not the cost centre; past that threshold `assert` records
  the bound and returns `Ok`, and the **complete** feasibility decision runs
  in `final_check`. Propagation stays the bound-implication probe and moves to
  the queue with lazy Farkas cores.
- **DL** keeps its incremental negative-cycle detection on `assert` — that is
  already the cheap-partial-check shape — and opts into the propagation queue
  and lazy explanation, so the cycle behind a propagated literal is walked and
  turned into literals only when conflict analysis reaches it.

### Slice 2 — one Boolean search (scoped here, not implemented here)

`CdclT`'s clause store and propagation are to be replaced by the native core's:
a flat clause arena with per-clause headers, two-watched literals with blocking
literals, and the native core's reduce/restart machinery — either by moving
`CdclT` onto `proof_sat`'s arena types, or by making `NativeIncrementalCdcl`
(ADR-1703) the CDCL(T) driver's search with the theory hooks of slice 1 wired
into its propagate/decide loop. The motivation is the measured **7x** above,
and the exit criterion is that `cdclt_solve_php_6_7` closes most of the gap to
`proof_sat_solve_php_6_7` with every existing verdict unchanged. It is a
separate lane because it touches the trail, the reason representation and the
1-UIP analysis all at once, while slice 1 does not touch propagation at all.

## Evidence

- Microbenchmark, 2026-09-05, same PHP(7,6) CNF, same host:
  `cdclt_solve_php_6_7` 39.6 ms vs the native core's 5.7 ms
  ([microbenchmarks-2026-09-05.md](../08-planning/microbenchmarks-2026-09-05.md)).
- Route ladders, 2026-08-21: `dl-online:BUDGET` on 64/65 traced QF_IDL misses
  and 51/55 traced QF_RDL misses; QF_LRA misses split 29 admission-cap / 36
  search
  ([diagnosis §2, §3](../05-algorithms/linear-arithmetic-deficit-diagnosis-2026-08-21.md),
  per-file data in `bench-results/linear-arithmetic-diagnosis-20260821/`).
- `lra_online.rs`'s module header, as of this commit, documents `assert` as
  re-deciding feasibility on every call — the design this ADR reverses.
- The interface shape is the standard one: Z3's `theory` carries
  `final_check_eh`, `new_eq_eh`/`new_diseq_eh`, and a lazy `get_antecedents`;
  MathSAT and cvc5 both separate a cheap `assertLiteral` from a complete
  `check(FULL_EFFORT)`. This ADR takes the final-check and lazy-explanation
  halves; equality/disequality callbacks and relevancy are deliberately left
  out (see Alternatives).

## Alternatives

- **Change `assert`'s signature to return `TheoryExplanation`.** Rejected:
  it edits all ten implementors for a laziness that buys nothing, because the
  driver consumes an assert conflict in the same step.
- **Make `propagate` take `&mut self` and keep returning a `Vec`.** Rejected:
  it is the same allocation with a different receiver. The queue is what
  removes the allocation and gives the theory a place to record progress.
- **Add `new_eq_eh` / `new_diseq_eh` and relevancy now.** Deferred. They pay
  off for theory *combination* (Nelson–Oppen equality propagation) and for
  large Boolean skeletons respectively; neither is the measured cause of the
  QF_IDL/QF_RDL/QF_LRA deficit. Adding them here would widen the trait past
  what any implementor in this slice uses, which is how a trait acquires
  methods with no test.
- **Do slice 2 first.** Rejected: the 7x is real, but a search rewrite lands on
  top of a theory interface that is about to change shape, and every theory
  conflict path would be re-verified twice. The interface is also the cheaper
  half.
- **Delete `CdclT` and route everything through `NativeIncrementalCdcl` with
  assumptions.** Rejected as an alternative to slice 2, not to this ADR:
  assumption-based theory interaction re-solves from scratch per round and
  loses the online trail, which is exactly what `CdclT` exists to provide.

## Consequences

**Easier.** A theory can now be expensive at the right moment: the complete
check runs once per total assignment instead of once per asserted literal.
Propagation reasons cost nothing until they are used. A theory that discovers
atoms during search — an interface-split lemma, a lazily-instantiated bound —
can register them through the trait rather than through a driver side table.

**Harder.** There are now two ways to answer a conflict (eager literals, lazy
handle) and two moments to detect one (`assert`, `final_check`), so a theory
author has a correctness obligation the four-method trait did not impose: a
handle must stay resolvable for as long as its literal is assigned. The
driver's abort-to-`Unknown` path exists because that obligation can be
violated, and it is tested with a mock theory that violates it deliberately.

**Revisited.** Slice 2 revisits `CdclT`'s search entirely; when it lands, the
propagation queue becomes the interface between the native core's trail and
the theory, and this ADR's `PropagationQueue` should not need to change.
`FinalCheckOutcome::Unknown` should be revisited if a theory ever wants to say
"unknown, but here is a lemma" — today it must choose one.

**Not claimed.** This ADR does not claim a corpus improvement. Slice 1's
measured effect on the QF_IDL and QF_LRA miss populations is reported with the
implementation; a widened interface that no theory used would move nothing,
and the two opt-ins are how it is tested against real files rather than only
against mocks.
