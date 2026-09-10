# ADR-1814: The eager/lazy array stage already exists and is capability-based; a cost-based stage waits until the eager certificate is on the shipping path

Status: accepted
Index-summary: ADR-0010's eager array elimination is kept, but STP's cost-based staged rule is NOT adopted yet — the staging already exists (the `Unsupported` refusal IS the lazy trigger at `abv.rs:739-744`, so the roadmap's "refused outright" is wrong for the main QF_ABV route), and the certificate a cost rule would trade away is unreachable from the default solve path (`certify_array_elim_unsat` has zero callers in `evidence.rs`), so the trade cannot be priced; the ordered prerequisite is to wire the certificate, then measure
Date: 2026-09-09

## Context

[ADR-0010](adr-0010-arrays-via-eager-elimination.md) chose eager array
elimination (read-over-write + Ackermann, QF_ABV → QF_BV). Roadmap item 4.2 of
[`docs/solver-comparison-2026-09/11-roadmap-and-plan.md`](../../solver-comparison-2026-09/11-roadmap-and-plan.md)
proposes keeping it but adopting STP's *staged* rule — eager only when the read
count is small and the estimated expansion cost is small, else refinement — on
the grounds that this "removes the `MAX_ARRAY_EQ_INDEX_BITS = 8` refusal", and
that the cost is a checkable UNSAT certificate no bit-vector reference solver
produces.

Two of that framing's three premises do not survive checking.

### Premise 1: "array equalities above the cap are refused outright" — WRONG for the main route

`const MAX_ARRAY_EQ_INDEX_BITS: u32 = 8;` is at
`crates/axeyum-rewrite/src/arrays.rs:31`, and exceeding it does produce
`Err(ArrayElimError::Unsupported)` from `eliminate_arrays`
(`arrays.rs:461-466`). But on the pure QF_ABV route that error is **consumed as
an admission test, and it is what engages the lazy path** —
`crates/axeyum-solver/src/abv.rs:739-744`:

```rust
match abstract_arrays_counted(arena, assertions) {
    Ok(_) => return check_qf_abv_lazy(backend, arena, assertions, config),
    Err(ArrayElimError::Ir(inner)) => return Err(SolverError::Backend(inner.to_string())),
    // The refused case: engage the lazy-ROW path below.
    Err(ArrayElimError::Unsupported(_)) => {}
}
```

So **a staged eager/lazy rule already ships.** What ships is a *capability*
stage, not a *cost* stage: the predicate is "can the eager pass express this?",
evaluated by running it and catching the refusal. The cap is an outright
refusal only where eager elimination is entered directly and not behind that
match — `combined.rs:73`, `aufbv.rs:57`, `proof.rs:733`/`:771` — where the auto
path converts it to an honest `Unknown` (`auto.rs:4809-4823`).

The cap is also narrower than "all array equalities". It is checked *after* the
write-index shortcut at `arrays.rs:435-459`: when both sides peel to the same
base array, equality is expanded only over the written indices and returns
before the cap is consulted, so a 64-bit-indexed store-chain equality over a
shared base is decided eagerly today. The cap bites only on equalities whose
sides do not share a peeled base.

### Premise 2: "eager buys us a certificate" — true of the code, false of the shipping path

`crates/axeyum-solver/src/abv/array_elim_certificate.rs` (386 lines) is real and
strong. `ArrayElimUnsatCertificate::recheck()` (`:158-234`) re-runs
`eliminate_arrays` on a scratch clone of the **original** assertions, runs an
independent `witness_read_over_write` sampling check, re-derives the select
congruence and demands exact structural equality, re-exports the QF_BV proof and
demands the DIMACS be byte-identical, and finally re-checks the DRAT. Its own
docstring records a measured 2026-09-06 mutation (swapped `Op::Store` `ite`
branches) that survives steps 3-5 and is caught only by the witness step — that
is a checker shown able to fail.

**But it is not reachable from a default solve.** `certify_array_elim_unsat`
appears **zero times** in `crates/axeyum-solver/src/evidence.rs`. Its only
non-test callers are `crates/axeyum-machine-evidence/src/symbolic_memory.rs:344`
and `:409` — the symbolic-memory artifact pipeline, not `check_auto` / `solve`.
The rest of its occurrences are the `mod`/`pub use` at `abv.rs:11193`/`:11197`,
two re-export lists in `lib.rs`, and a `config_registry.rs` note. (The inventory
doc `docs/solver-inventory-2026-09/05-bitvector-arrays-fp-and-datatypes.md:185`
labels it `WIRED` and cites `abv.rs:10972`; the line number is stale and "wired"
there means *exported*, not *on the solve path*.)

So today, for an ordinary QF_ABV query, **"eager" and "certified" are not the
same set.** Eager decides; the certificate is produced by a different entry
point that dispatch never calls.

### Premise 3: the lazy arm's evidence — confirmed, and it is nothing

Item 1.1a landed `RowEngine` (`abv.rs:3338-3343`), a warm `IncrementalBvSolver`
held across CEGAR rounds and routed from `auto.rs:5494`. It changes the cost of
the lazy arm; it changes nothing about its evidence. The lazy ROW arm's unsat is
constructed at `abv.rs:3535`:

```rust
// The abstraction is a relaxation; its UNSAT implies the original's.
CheckResult::Unsat => return Ok(CheckResult::Unsat),
```

`CheckResult::Unsat` is a unit variant (`backend.rs:24-25`) — no payload. The
identical construction is at `abv.rs:140` for the lazy select-congruence
sibling. Evidence is assigned later and independently in `evidence.rs`, and for
a query the lazy arm decided — which by construction means eager elimination
refused — the reduction-certificate arm `reduction_unsat_certificate`
(`evidence.rs:4594`) calls `export_qf_aufbv_unsat_proof_within`
(`proof.rs:766`), whose first act is `eliminate_arrays(...)?` (`proof.rs:771`),
which errors for the same reason. The result is the bare `Evidence::Unsat(None)`
at `evidence.rs:3826`.

Worse for the proposal: on the **warm** rounds there is no DRAT at all.
`RowEngine::solve_round_warm` reaches `IncrementalCnf::solve_with_limits` →
`IncrementalSat::solve_with_limits` (`crates/axeyum-cnf/src/lib.rs:810`) backed
by `NativeIncrementalCdcl` — no `solve_with_drat_proof*` on that path. On cold
rounds a DRAT exists but refutes the abstraction-plus-lemmas CNF, not the
original array formula, is only checked when `config.prove_unsat` is set
(`sat_bv_backend.rs:2301`, `:2393`, `:2408`), and is discarded.

### The STP numbers, and a correction

`references/` in this tree holds one file, `README.md`; `references/stp/` is
**ABSENT** and STP is not even in `scripts/fetch-references.sh`'s repo list. The
only in-repo evidence is the committed quotation at
[`docs/solver-comparison-2026-09/04-bitwuzla-boolector-stp.md:690-696`](../../solver-comparison-2026-09/04-bitwuzla-boolector-stp.md),
which cites `STP.cpp:713-745` for the rule and `:731-736` for the comment
measuring deep store chains at "48x longer than leaving them to read
refinement". Treat that as a second-hand citation, not a verified source read.

**Correction to the constants as stated in the roadmap:** STP's literals are
`arrayReadLimit = 10` (50 under `--ackermannisation`) and
`arrayEagerCostPerRead = 20`; the cost threshold is the *product*
`arrayReadLimit × 20`. "Expansion cost < 200" is therefore a derived default,
not a source constant — under `--ackermannisation` the same rule reads 1000.

### What decides between our array routes today

Nine distinct array decision procedures across five top-level dispatch routes
(`auto.rs:1696-1708`, `:4728-4732`, `:5415-5470`, `:4776`), and the gates are
**boolean `Features` flags** — `has_array`, `has_non_bv_array`, `has_function`,
`has_int`, `has_real`, `has_uninterpreted_sort`, `has_datatype`,
`has_non_bool_bv_array` — plus the capability test above. The only
budget-shaped knobs are wall-clock (`abv_online_reserve_policy` at
`auto.rs:4925`; `TIMED_ARRAY_REFUTER_SLICE = 250ms` at `auto.rs:5406-5413`).
**No array-read-count or expansion-cost predicate exists anywhere.** The nearest
analogue in the tree is for UF, not arrays: `refuse_oversized_ackermann`
(`combined.rs:85-89`).

## Decision

**Keep ADR-0010's eager elimination, and do NOT adopt STP's cost-based staged
rule yet — because the capability-based stage already ships, and the certificate
a cost rule would trade away is not on the shipping evidence path, so the trade
has no price today; the ordered prerequisite is to route
`certify_array_elim_unsat` through `evidence.rs` so that "decided eagerly" and
"certified" become the same set, and only then measure whether a cost predicate
should move queries off it.**

Four commitments:

1. **ADR-0010 stands.** Eager elimination remains the route we prefer when it
   is admissible.
2. **No cost predicate is added now.** Adding one would move queries from the
   arm that *can* be certified to the arm that produces `Evidence::Unsat(None)`,
   on a speed argument we have not measured on our own corpora, while the
   certificate is not being emitted from either arm. That is spending evidence
   we have not yet collected in exchange for a speedup we have not yet seen.
3. **The prerequisite is wiring, not algorithms.** `certify_array_elim_unsat`
   must have a caller in `evidence.rs` on the QF_ABV unsat path, and the
   resulting certificate must be counted — the roadmap's standing metric,
   "count of `Evidence::Unsat(None)` construction sites", is 8 today (all in
   `evidence.rs`: `:2162`, `:2282`, `:2348`, `:2406`, `:2643`, `:3144`,
   `:3814`, `:4119`) and does not distinguish an array unsat from any other.
   The number that matters for this ADR is finer: **what share of QF_ABV unsat
   verdicts carry an `ArrayElimUnsatCertificate`.** It is 0 today, by
   construction, and nothing measures it.
4. **Raising or removing `MAX_ARRAY_EQ_INDEX_BITS` is a separate question** and
   is not blocked by this ADR. It is not, on the main route, a source of
   `unknown`; it is a route selector. Changing it changes which arm decides, and
   therefore which evidence class the answer lands in — so it should be changed
   *after* commitment 3, when that consequence is visible.

## Evidence

- `crates/axeyum-rewrite/src/arrays.rs:31` (the cap), `:435-459` (the shortcut
  that runs before it), `:461-466` (the refusal).
- `crates/axeyum-solver/src/abv.rs:739-744` — the refusal consumed as the lazy
  trigger. This is the single observation that falsifies "refused outright".
- `grep -c certify_array_elim_unsat crates/axeyum-solver/src/evidence.rs` → **0**.
  Non-test callers: `crates/axeyum-machine-evidence/src/symbolic_memory.rs:344`,
  `:409`, and nothing else.
- `crates/axeyum-solver/src/abv.rs:3535` and `:140` — the lazy arms'
  payload-free `CheckResult::Unsat`.
- `crates/axeyum-solver/src/abv/array_elim_certificate.rs:158-234` — the
  five-step `recheck`, and `:65-77`, the recorded mutation that only step 2
  catches.
- The STP quotation at
  `docs/solver-comparison-2026-09/04-bitwuzla-boolector-stp.md:690-696`, flagged
  above as second-hand because `references/stp/` is absent.

## Alternatives

- **Adopt STP's rule now, as roadmap 4.2 proposes.** Rejected: its stated
  benefit ("removes the `MAX_ARRAY_EQ_INDEX_BITS` refusal") is already delivered
  by the existing capability stage on the main route, and its stated cost
  (losing the certificate) is mispriced at zero because the certificate is not
  shipping. Adopting it would produce a real, unmeasured regression in the
  certified population and a speedup we have no number for.
- **Adopt the rule *and* wire the certificate in the same change.** Rejected as
  a sequencing error, not on merit. Wiring the certificate changes what the
  ledger reports; adding a cost predicate changes which queries reach it. Doing
  both at once makes the resulting certified-share number uninterpretable —
  you cannot tell whether it moved because evidence started shipping or because
  queries were rerouted away from it.
- **Make the lazy arm certifiable instead, and then stage freely.** The right
  long-run answer, and deliberately not this ADR's decision. It is a real
  research item — the lazy arm's refutation is over an abstraction plus
  materialized ROW lemmas, so a certificate has to carry the lemma set and its
  justification, and the warm path currently produces no DRAT at all. That is a
  larger piece of work than 4.2 was sized as, and it should get its own ADR.
- **Declare the question undecidable on present evidence.** Considered, and
  rejected: the two observations above (the fallback at `abv.rs:739-744`, the
  zero callers in `evidence.rs`) are enough to decide *not to act yet* and to
  name what has to be true first. That is a decision, not a deferral.

## Consequences

**What this buys.** The `MAX_ARRAY_EQ_INDEX_BITS` cap stops being described as a
capability hole in comparison prose — on the main QF_ABV route it is a route
selector, and saying otherwise overstates a gap against Bitwuzla/Boolector/STP
that we do not have. It also puts a number on the certificate claim before we
make it: "we produce an array-elimination UNSAT certificate nobody else can" is
true of the code and false of the shipping path, and this ADR says so in
writing.

**What is LOST by deciding this way.**

- **We forgo whatever speed the cost rule would buy, for at least one more
  cycle.** If STP's 48x on deep store chains transfers to our corpora, we are
  paying it on every eagerly-admitted deep chain until commitment 3 and the
  measurement land. We have no measurement saying it does transfer, and none
  saying it does not — that is the honest state.
- **We accept, for now, that the fast lazy arm is the uncertified arm.** Item
  1.1a made lazy faster; this ADR declines to make it *more used*. The
  performance-versus-evidence tension is not resolved, it is sequenced.
- **A staged rule, when it comes, WILL trade evidence for speed, and that trade
  will be acceptable only under a stated bound.** Stating it now so it is not
  relitigated: a cost rule may route a query to an uncertified arm only if the
  certified share of QF_ABV unsat verdicts is *measured before and after* and
  the drop is reported, not discovered. An arm that produces no certificate is a
  capability regression against our own identity; it is tolerable when it is
  counted and intolerable when it is silent.

## What would falsify this decision

1. **A public QF_ABV corpus measurement (roadmap 3.8) showing eagerly-admitted
   deep store chains cost us decided instances at a realistic budget.** If the
   48x is real on our corpora and is losing verdicts, the speed side outweighs
   an evidence route that is not yet shipping, and the cost rule should land
   first with the wiring following.
2. **`certify_array_elim_unsat` turns out to be unroutable from `evidence.rs`
   at acceptable cost** — for instance if re-running `eliminate_arrays` and
   re-exporting a byte-identical DIMACS on every array unsat is prohibitive.
   Then commitment 3 is not a prerequisite but a separate project, and the
   staging question must be re-decided without it.
3. **The certified share, once measured, turns out to be small even on the
   eager arm** — because `MAX_ARRAY_ELIM_CONGRUENCE_PAIRS = 256`
   (`array_elim_certificate.rs:84`) declines above an `O(k²)` pairing bound that
   nothing has measured. If most eagerly-decided queries exceed it, then "eager
   is the certified arm" is false for a second reason and the whole trade
   collapses to a pure speed question.
4. **Someone shows the lazy ROW arm's refutation can carry a checkable
   certificate cheaply.** That removes the trade entirely and makes the cost
   rule free; this ADR should then be superseded rather than amended.
5. **`references/stp` is fetched and the quoted rule or the 48x comment is not
   there, or reads differently.** The staged rule's provenance is currently a
   second-hand citation; if it is wrong, the design being deferred is not the
   design STP actually ships and the comparison should be redone.
