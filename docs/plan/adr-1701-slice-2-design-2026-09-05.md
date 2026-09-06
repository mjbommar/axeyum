# ADR-1701 slice 2 — measured hook cost and the design for attaching a theory to the native core, 2026-09-05

Lane `native-core-theory-hook-spike`. This is a **spike memo**: it reports a
measurement and a design, and the code it measures
(`crates/axeyum-cnf/src/proof_sat/theory.rs` plus the generic parameter on
`Cdcl`) may be thrown away. Nothing here changes a shipping default — every
`solve_with_drat_proof*` entry point still constructs the search with
`NullTheory` and still emits the same DRAT stream.

It answers the risk
[ADR-1701](../research/09-decisions/adr-1701-the-theory-interface-gains-final-check-a-driver-owned-queue-lazy-explanation-and-dynamic-atoms.md)
scoped but did not measure: **slice 2 wants to move CDCL(T)'s Boolean search
onto the native core (`crates/axeyum-cnf/src/proof_sat.rs`), and the native
core has no theory hooks. What does adding them cost?**

Read alongside:

- [ADR-1703](../research/09-decisions/adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md)
  — the native core is *the* SAT engine.
- [2026-09-05 slice-1 measurement](../research/11-design-review/2026-09-05-adr-1701-slice-1-measured.md)
  — the QF_IDL timeouts spend 18–20 s of a 24 s budget in the CDCL(T) driver's
  own Boolean propagation with theory cost at or under 0.1 s.
- [microbenchmarks-2026-09-05](../research/08-planning/microbenchmarks-2026-09-05.md)
  — `CdclT::solve` 39.6 ms vs `solve_with_drat_proof` 5.7 ms on identical
  PHP(7,6) CNF.
- [2026-09-05 SAT/SMT performance and architecture review](../research/11-design-review/2026-09-05-sat-smt-performance-and-architecture-review.md)
  §3.2 D1 and D2.

---

## 1. Result in one line

**Design A — hooks called unconditionally with empty `#[inline]` bodies —
costs 6.3% of the native core's PHP runtime. Design B — the same hooks behind
an associated `const HAS_THEORY: bool` the search consults — costs nothing
measurable. Use design B.**

The hook design therefore passes the acceptance bar, and the measured cost of
carrying theory hooks in the native core is **zero for every existing
caller**. Adding a theory interface to `proof_sat.rs` is not what would make
slice 2 expensive.

---

## 2. What was built

A crate-private `axeyum_cnf::proof_sat::theory` module mirroring
`axeyum_solver::euf_egraph::TheorySolver` as ADR-1701 widened it:

```rust
pub trait NativeTheory {
    const HAS_THEORY: bool = true;
    fn assert(&mut self, var: usize, value: bool) -> Result<(), Vec<CnfLit>>;
    fn push(&mut self);
    fn pop(&mut self);
    fn propagate_into(&mut self, queue: &mut PropagationQueue);
    fn final_check(&mut self) -> FinalCheckOutcome { FinalCheckOutcome::Sat }
    fn explain(&mut self, handle: ExplanationId) -> Option<Vec<CnfLit>> { None }
    fn take_new_atoms(&mut self) -> usize { 0 }
}
```

plus `PropagationQueue`, `TheoryExplanation`, `ExplanationId` and
`FinalCheckOutcome`, each with the same shape as its `euf_egraph` counterpart
but over `CnfLit` rather than `TheoryLit`.

**It cannot be the same trait.** `axeyum-cnf` sits *below* `axeyum-solver` in
the dependency graph. The adapter in slice 2 proper is therefore a blanket
`impl NativeTheory for T where T: TheorySolver` written on the solver side,
translating literals at the boundary. The shape is kept identical precisely so
that adapter is mechanical, not a redesign.

`Cdcl` gained a third generic parameter, `T: NativeTheory = NullTheory`. Every
existing public function keeps its signature: `Cdcl::new`/`Cdcl::new_empty`
live in an impl specialised to `NullTheory` and delegate to a generic
`new_with_theory`.

Call sites wired:

| hook | where in `search_loop` |
|---|---|
| `assert` | `theory_round`, over the trail suffix since the last round, after Boolean propagation reaches a conflict-free fixpoint |
| `propagate_into` | same round, after the asserts drain |
| `take_new_atoms` | same round, last |
| `final_check` | the `pick_branch() == None` branch, immediately before `sat` is reported |
| `push` | `push_level`, paired with every `trail_lim.push` |
| `pop` | `backtrack_to` (one per level removed, *before* the trail is truncated) and `reset_search_state` |
| `explain` | not wired — see §6, the reason-representation risk |

**The DRAT and `check_lrat` contracts are untouched.** A theory conflict, a
theory propagation or a dynamically registered atom is *recognised* and then
**declined**: the search returns `SearchOutcome::Interrupted`, the undecided
outcome. That is deliberate and it is the load-bearing open question for slice
2 (§6.1).

### Hook liveness is falsifiable

A benchmark that shows "no cost" because the hooks are never reached is
worthless. Five tests in `proof_sat::tests::theory_hooks` make the call sites
falsifiable:

- a counting theory asserts each hook is reached and that `final_check` fires
  **exactly once** (at the one total assignment);
- an unsat run asserts the hooked search emits a DRAT proof **byte-identical**
  to the `NullTheory` path — not merely the same verdict, the same derivation;
- three adversarial theories (conflicting `assert`, refusing `final_check`,
  propagating) assert the search never turns their answer into `sat` or
  `unsat` and never emits a proof step.

Mutation-verified: disabling the `theory_round` call site kills **4 of the 5**.

---

## 3. The measurement

### Method

- BEFORE is `d9dc21af3`, extracted with `scripts/lane-snapshot.sh` (`--touch`
  stamped, so cargo's mtime freshness check is not fooled). AFTER is this
  lane's worktree.
- Both arms built through `scripts/cargo-serialized.sh`; the resulting
  binaries were confirmed to **differ by `sha256sum`** before every sweep.
- Runs use the **prebuilt binaries** under `taskset -c 0-7`, not
  `cargo-serialized.sh` — that wrapper takes a host-wide flock, so timing
  through it measures the queue.
- Five interleaved before/after pairs per benchmark. `/proc/loadavg` recorded
  at each sweep boundary; the host is shared with other lanes throughout
  (load 9–25 across these sweeps).

### 3.1 PHP(7,6), `axeyum-cnf/benches/proof_sat_solve.rs`

Criterion `--warm-up-time 1 --measurement-time 5`. Figures are criterion's
point estimate per run.

**Design A** (hooks called unconditionally; commit `3e0a09e4f`):

| arm | run 1 | run 2 | run 3 | run 4 | run 5 | min | median | max |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| BEFORE | 2.750 | 2.665 | 2.652 | 2.656 | 2.664 | 2.652 | 2.664 | 2.750 |
| AFTER A | 2.818 | 2.832 | 2.819 | 2.838 | 2.738 | 2.738 | 2.819 | 2.838 |
| pairwise Δ | +2.5% | +6.3% | +6.3% | +6.9% | +2.8% | | **+6.3%** | |

(ms). Every pair is positive and the two arms' ranges barely overlap. This is
a real cost, not noise.

**Design B** (`HAS_THEORY` consulted at every theory site; commit `925efbebc`):

| arm | run 1 | run 2 | run 3 | run 4 | run 5 | min | median | max |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| BEFORE | 2.828 | 2.782 | 2.753 | 2.704 | 2.664 | 2.664 | 2.753 | 2.828 |
| AFTER B | 2.763 | 2.697 | 2.749 | 2.702 | 2.665 | 2.665 | 2.702 | 2.763 |
| pairwise Δ | −2.3% | −3.1% | −0.2% | −0.1% | +0.05% | | **−0.2%** | |

Indistinguishable from zero, and well inside the within-arm spread (both arms
drift about 6% downward across the five runs as host load falls from 25 to 10,
which is why the *pairwise* column is the number to read, not the medians).

**Why A costs and B does not.** `theory_round` walks the trail suffix once per
propagation fixpoint — a second `qhead` cursor over data `propagate` already
walked. An empty callee does not make an empty loop. `HAS_THEORY` is an
associated `const`, so for `T = NullTheory` the whole function body, loop
included, is dropped at monomorphization.

### 3.2 Control arm: `axeyum-solver/benches/cdclt_propagate.rs`

`CdclT` is untouched by this change, so this arm should not move.

| arm | min | median | max |
|---|---:|---:|---:|
| BEFORE (design-B sweep) | 33.66 | 38.82 | 43.90 |
| AFTER B | 34.03 | 40.90 | 44.33 |

(ms). It does not move, but it also **cannot resolve anything below about
30%** on this host: the same binary spans 33.7–43.9 ms across five runs. It is
reported for completeness, not as evidence. The design-A sweep gave the same
picture (BEFORE 32.49/32.66/40.54, AFTER 32.43/32.77/40.32).

Incidentally: at 2.7 ms vs 33–40 ms on the same PHP CNF and the same host on
the same day, the native core is **12–15x** faster than `CdclT` here, not the
7x recorded on 2026-09-05. Both numbers are load-dependent; the gap is not in
doubt, its size is.

### 3.3 Real CNF: p4dfa, 20 files at a 20 s budget

CNFs dumped with the unmodified
`crates/axeyum-bench/examples/dump_dimacs.rs` (the same tool
`bench-results/sat-core-gate-b-20260905/` used), 20/20 dumped, 0 failures.
Selection: **all 6 files the gate-(b) run recorded the native core deciding**,
plus the **14 smallest** of the remaining 107 by CNF variable count — a
deliberate, declared selection so the "decided count unchanged" test has
content, not a random sample.

Driven by a new `crates/axeyum-cnf/examples/native_core_sweep.rs` (native core
only; `gate_b_sweep` carries `required-features = ["batsat-reference"]` and
would double the wall time by running BatSat alongside). Identical source in
both arms; the two built binaries confirmed to differ by `sha256sum`. Every
`sat` verdict is checked with `CnfFormula::evaluate` before it is recorded and
the sweep's exit status fails on an invalid model.

| | BEFORE | AFTER (design B) |
|---|---:|---:|
| decided (sat+unsat) | **8 / 20** | **8 / 20** |
| verdict disagreements | — | **0** |
| invalid models | 0 | 0 |
| total wall, single shot | 271,991 ms | 280,504 ms (**+3.13%**) |
| total wall, noisy files re-measured | 269,171 ms | 272,223 ms (**+1.13%**) |
| the 12 timeout files only | 241,223 ms | 242,539 ms (**+0.55%**) |

The single-shot +3.13% is **one file**: `compose.s2._bit8_na6_nr3_paired.cnf`
came out 7,949 ms → 14,630 ms (+84%). Re-running it four times per arm shows
that is host noise, not a trajectory change:

| file | BEFORE ×4 (ms) | AFTER ×4 (ms) |
|---|---|---|
| `compose.s2._bit8_na6_nr3_paired` | 8661, 6542, 5955, 6008 | 8903, 7131, 6665, 5234 |
| `mobiledevice_bit8_na6_nr3_paired` | 3147, 3234, 3147, 3065 | 3152, 3153, 3112, 3169 |
| `string1x8.4._bit8_na6_nr3_paired` | 13593, 13523, 13217, 16144 | 13671, 13834, 16538, 14434 |

The ranges overlap heavily on the two long SAT instances and are flat on the
short one. Substituting the medians for those three files gives the +1.13%
row. The largest and least noisy population — the 12 timeout files, 89% of the
total wall — moves **+0.55%**.

### 3.4 Acceptance verdict

| bar | result |
|---|---|
| PHP bench within the measured noise band | **PASS** (design B, −0.2% pairwise median; design A **FAIL** at +6.3%) |
| p4dfa decided count unchanged | **PASS** (8/20 both arms, 0 disagreements) |
| p4dfa total time within 3% | **PASS** (+1.13% re-measured; +0.55% on the timeout population; the raw +3.13% single shot is one noisy file) |

---

## 4. How `DlTheory` and `LraTheory` would attach

### 4.1 Atom-to-variable mapping

`TheorySolver::assert(atom: usize, value: bool)`'s `atom` is already the
driver's **SAT variable index** in every in-tree implementor, and `CdclT`
keeps the alignment in a per-variable side table
(`cdclt.rs`: "Per SAT variable, the aligned theory atom when this variable is
mirrored into the theory"). `NativeTheory::assert(var, value)` takes the same
convention, so the blanket adapter is a straight forward. The native core's
`CnfVar`/`CnfLit` are zero-based dense indices, exactly like `Lit { var,
positive }`, so the translation is a field rename, not a remap.

### 4.2 Decision-level alignment

`push_level` is the single point that opens a decision level, and it pairs
`trail_lim.push` with `theory.push()` unconditionally, so
`trail_lim.len() == theory push depth` holds **by construction** rather than by
discipline. `backtrack_to(level)` pops `trail_lim.len() - level` times *before*
truncating the trail, so a theory that walks the driver's trail during `pop`
still sees the assignments it is undoing. That ordering is not optional and it
is the first thing to re-check if a real theory misbehaves.

One gap the spike does **not** close: `reset_search_state` (the warm
incremental path, `NativeIncrementalCdcl`) pops one level per level this solve
pushed, but level-zero assertions made before the first `push` are not undone —
`TheorySolver` has no backtrack point below level zero. For a one-shot solve
that is correct. For a **warm** CDCL(T) across solves, slice 2 must decide
between a new trait method (`reset`) and a fresh theory instance per solve.

### 4.3 Theory conflict as a learned reason clause

This is the hard part and the spike deliberately declines it (§6.1). The design
when it lands:

- An `assert` conflict arrives eagerly (`Vec<CnfLit>`) at the current decision
  level, so it can go straight into 1-UIP `analyze` as a conflict clause, once
  the clause has been allocated in the arena.
- A `final_check` conflict is **not** required to name a current-level literal.
  ADR-1701 already states the rule: backjump to the highest decision level the
  core names before analysing it, or `analyze`'s `path_count` underflows. In
  the native core that is `backtrack_to(max_level(core))` followed by the normal
  conflict path; an all-level-zero core yields the empty asserting clause, which
  is the correct `Unsat`.

### 4.4 Theory propagation with a lazy reason

`enqueue(lit, reason: Option<CRef>)` can only name an arena clause. Two ways
to carry a lazily-explained implication:

- **(i) Eager materialisation.** Resolve the handle at propagation time,
  allocate the reason clause, `enqueue(lit, Some(cref))`. Zero change to the
  hot path and zero change to `analyze`. Cost: it throws away exactly the
  saving ADR-1701's lazy explanation exists to capture — most propagated
  literals are never resolved against.
- **(ii) A reason enum.** `enum Reason { None, Clause(CRef), Theory(ExplanationId) }`
  in place of `Option<usize>`, with `analyze` resolving a `Theory` reason
  through `explain` and allocating the clause only then. This is the design
  that pays, and it is **the unmeasured cost of slice 2** — `reason` is read on
  every step of every conflict analysis and in `lit_redundant`'s recursive
  minimization.

Recommendation: land (ii) directly, but measure it as its own before/after on
the same PHP bench before wiring any theory to it. A `Reason` that is still one
word (a tagged `u64`, `CRef` and `ExplanationId` both being indices) is the
shape to aim for; the naive three-variant enum is likely to widen the array.

### 4.5 Where `final_check` sits relative to restarts and `reduce_db`

The spike puts `theory_round` **before** the restart check and puts
`final_check` at the `pick_branch() == None` branch. Both placements are
deliberate:

- Before the restart check, so the theory sees every assignment on the trail
  that produced the decision to restart, and so a `theory_round` conflict is
  never discarded by a restart that has already happened.
- `reduce_db` runs only on the conflict side of the loop, after a backjump and
  before propagation. Since a theory reason clause would be allocated on the
  *other* side (during `theory_round` or `final_check`), it cannot be deleted
  between being emitted and being used *in this shape*. When (ii) lands and
  theory reason clauses are allocated lazily during `analyze`, that changes:
  a theory reason clause must be locked exactly as `is_locked` locks a
  propagation reason, or `reduce_db` can delete the justification of an
  assigned literal. That is a soundness obligation, not a performance note.

---

## 5. What `CdclT`'s callers would need

Ten production `CdclT::new` call sites, all in `axeyum-solver`:

| file | line |
|---|---:|
| `crates/axeyum-solver/src/lib.rs` | 719 |
| `crates/axeyum-solver/src/euf_egraph.rs` | 798 |
| `crates/axeyum-solver/src/dl_online.rs` | 2077 |
| `crates/axeyum-solver/src/lra_theory.rs` | 281 |
| `crates/axeyum-solver/src/lia_theory.rs` | 211 |
| `crates/axeyum-solver/src/uflra_online.rs` | 1354 |
| `crates/axeyum-solver/src/uflia_online.rs` | 1709 |
| `crates/axeyum-solver/src/ufbv_online.rs` | 1378 |
| `crates/axeyum-solver/src/string_theory.rs` | 1061 |
| `crates/axeyum-solver/src/qinst_egraph.rs` | 2487 |

plus `crates/axeyum-solver/benches/cdclt_propagate.rs:83` and ~20 more inside
`cdclt.rs`'s own test module. (`cdclt.rs`'s thread-local `TheoryLayerStats`
opt-in doc already says "~10 `CdclT::new` call sites"; this is that list,
enumerated.)

They all pass `(var_count, atom_count, clauses: Vec<Vec<Lit>>, deadline)` and
then call `solve(&mut theory)`. If slice 2 keeps that constructor signature and
swaps the *body*, no caller changes at all. That is the cheap path and it is
worth protecting.

### What breaks

1. **`TheoryLayerStats` instrumentation** (`crates/axeyum-solver/src/layers.rs:440`,
   consumed by `crates/axeyum-bench/examples/smtcomp_cli.rs`'s
   `; theory-layer …` trace line). Thirteen fields, and the ones that are
   *driver*-side rather than theory-side have no counterpart in the native
   core: `boolean_propagate` (times `CdclT::unit_propagate`),
   `conflict_analysis` (times `CdclT::analyze_conflict`), `decisions`,
   `restarts`. The slice-1 measurement note is built entirely on these
   columns; losing them would make slice 2 unmeasurable by the same
   instrument that justified it. **Port the counters into `proof_sat.rs`
   before moving the search, not after.** They are cheap (`Instant` deltas
   already gated on a thread-local opt-in), and the native core already has
   the `ProofSearchProgress` hook as a precedent for an output-only,
   trajectory-neutral observer.
2. **`bench_internals` exposure** (`crates/axeyum-solver/src/lib.rs:252`,
   re-exporting `CdclT`, `Lit`, `Outcome` behind the `bench-internals`
   feature) and `benches/cdclt_propagate.rs`. If `CdclT` becomes a thin
   wrapper the bench still compiles and still measures the right thing. If
   `CdclT` is deleted, the bench and the microbenchmark note's headline ratio
   go with it — keep the bench pointed at whatever the CDCL(T) entry point is
   called after the move, or the 7x claim loses its meter.
3. **Dynamic atom registration after Tseitin auxiliaries.** `CdclT` notes that
   "dynamic theory variables may follow Tseitin auxiliaries" and maintains the
   alignment in a driver side table. The native core's `ensure_vars` already
   grows every per-variable table monotonically and `add_input_clause` already
   appends a *problem* clause after learned clauses exist (that is what the
   per-clause `learned` flag was introduced for). So the mechanism exists; what
   does not exist is the *ordering* contract — a theory that registers an atom
   mid-search needs the new variable added, marked branchable, and inserted
   into the order heap at a point where the trail is consistent. `theory_round`
   is that point, and `take_new_atoms` returning non-zero is the signal. The
   spike declines it rather than guessing.

---

## 6. Two routes, and which one lands the IDL files sooner

The coordinator's profile measurement changes the framing here, and it was
verified independently in source for this memo:
`CdclT::unit_propagate` (`crates/axeyum-solver/src/cdclt.rs:702`) is

```rust
while changed {
    for ci in 0..self.clauses.len() {
        for &lit in &self.clauses[ci] { ... }
```

— a **full clause-database rescan per fixpoint pass**, with no watch lists and
no blocking literals, and it clones the reason clause
(`self.clauses[ci].clone()`) on every unit implication. On the QF_IDL timeout
population that is 19.4 s of a 24 s budget (87% of wall) with theory cost at
0 ms. **So the 7x is not arena-vs-`Vec<Vec>` polish; it is asymptotic**:
O(passes × database) against O(assignments × watch-list length).

That admits a second route the ADR did not scope.

### Route A — slice 2 as scoped: move CDCL(T) onto the native core

Move `CdclT`'s search to `proof_sat`'s arena, watches, VSIDS heap, LBD tiers,
restarts and `reduce_db`, with the hooks this memo measures.

- **Cost.** The hook interface itself: **zero measured runtime, ~200 lines,
  already written.** The rest is the real work: the reason representation
  (§4.4 (ii)), the DRAT contract under theory lemmas (§6.1), porting
  `TheoryLayerStats`, dynamic atom registration, and re-validating every
  theory conflict path in ten adapters. Not one lane.
- **Gets.** The full native feature set at once — watches *and* blocking
  literals *and* VSIDS *and* LBD-tiered `reduce_db` *and* target rephasing —
  plus one Boolean engine instead of three (D1 closed, not narrowed).

### Route B — the contained fix: give `CdclT` two-watched literals in place

Add `Watch { clause, blocker }` lists and per-clause headers to `CdclT`,
copying `proof_sat.rs`'s design, and leave everything else — the theory
integration, `TheoryLayerStats`, the ten call sites, the reason representation,
`analyze_conflict` — untouched.

- **Cost.** Bounded and local: one propagation function, one clause store, one
  `backjump` that must reset the watch cursor. No trait change, no caller
  change, no proof-contract question, and `TheoryLayerStats::boolean_propagate`
  keeps measuring the same thing before and after, so it is its own scoreboard.
- **Gets.** The asymptotic fix and nothing else. No blocking literals unless
  they are copied too (they are cheap and should be), no LBD tiers, no
  `reduce_db`, no target rephasing.

### Which lands the IDL files sooner, and which is the end state

**Route B lands them sooner, and it is not wasted work.** The QF_IDL timeout
population's bottleneck is one function; route B replaces that function, and
route A replaces it as part of a much longer change. Since 87% of wall on that
population is inside `unit_propagate`, route B is where essentially all of the
available IDL headroom is.

**Route A is the right end state**, for the reason ADR-1703 already gives: one
SAT engine, one place where restarts and clause deletion are tuned, one place
where a proof is emitted. Route B leaves two engines and guarantees the second
one drifts.

**B is a stepping stone to A, not a detour**, provided one rule is followed:
*port the native core's `Watch`/`ClauseHeader`/`propagate` design verbatim
rather than inventing a second one.* Then route A's later move is a deletion
(drop `CdclT`'s copy, keep the callers) instead of a reconciliation of two
watch schemes. If instead route B grows its own bespoke watch code, it becomes
exactly the wasted work the question asks about.

**Recommended order:** B first (it is the IDL scoring lane), then the reason
representation (§4.4 (ii)) measured on its own, then the DRAT/theory-lemma
contract (§6.1), then A. The hook interface this memo measures is a
prerequisite for A only, and it is done and free.

### 6.1 The unresolved contract: a theory lemma is not RUP

The native core's identity is that every learned clause is RUP by construction,
so the learned sequence *is* a valid DRAT proof and `check_drat` /
`check_lrat` make `unsat` sound regardless of search bugs. **A theory lemma is
not RUP against the CNF.** Putting one into the learned database silently
converts the emitted proof from a refutation into a refutation-modulo-theory,
with nothing in the artifact saying so.

That is why this spike declines every theory-derived clause rather than
learning it. Slice 2 must pick one, and this is the decision to make **first**,
because it constrains everything else:

1. **Emit theory lemmas as labelled additions** and define a proof format that
   carries them (DRAT+lemmas / an LRAT dialect with theory steps), with the
   checker either trusting them or discharging them against the theory.
2. **Keep two streams**: the RUP-only DRAT for the Boolean part, plus a
   separate list of theory lemmas as assumptions of the refutation. Honest,
   and it makes the assumption count a visible metric — which fits this
   repository's "trusted base, not output volume" rule.
3. **Suppress proof emission whenever a theory is attached** and accept that
   CDCL(T) `unsat` carries no DRAT. That is what `CdclT` does today, so it is
   not a regression, but it forecloses proof-producing SMT.

(2) looks right for this tree. It is a decision that wants its own ADR.

---

## 7. Slice plan, with the IDL timeout population as the scoring target

The scoring target is the 50-file QF_IDL timeout population in
`bench-results/adr-1701-slice-1-20260905/qf_idl_population.tsv` (0/50 decided
in both arms of the slice-1 measurement), with
`qf_lra_population.tsv` (33 files, 5/33 after slice 1) as the secondary.

| # | slice | exit criterion |
|---|---|---|
| 1 | **`CdclT` gets two-watched literals + blocking literals**, ported verbatim from `proof_sat.rs`. No trait, caller or proof change. | `TheoryLayerStats::boolean_propagate` falls on the 5 traced IDL files; decided count on the 50-file IDL population rises from 0; zero verdict changes anywhere. |
| 2 | **Reason representation**: `Option<CRef>` → a one-word tagged `Reason` in `proof_sat.rs`, `analyze`/`lit_redundant` updated, `explain` wired. No theory attached yet. | `proof_sat_solve_php_6_7` within the noise band on its own before/after; p4dfa decided unchanged. |
| 3 | **ADR: the proof contract under theory lemmas** (§6.1), then implement it. | A CDCL(T) `unsat` produces an artifact whose theory assumptions are enumerable and counted. |
| 4 | **Move CDCL(T) onto the native core** behind the hooks this memo measured, `TheoryLayerStats` ported first. `CdclT::new`'s signature preserved so the ten call sites do not move. | `cdclt_solve_php_6_7` closes most of the gap to `proof_sat_solve_php_6_7`; every existing verdict unchanged across the corpus regression suite. |
| 5 | **Dynamic atom registration** through `take_new_atoms`, retiring the driver side tables. | The QF_LRA 1,024-atom admission cap (29 excluded files in the slice-1 note) becomes reviewable, since atoms no longer have to be known up front. |

Slices 1 and 2 are independent and can run in parallel. 3 gates 4. 5 follows 4.

---

## 8. Risks I cannot measure from here

- **The reason-representation cost (§4.4 (ii)) is unmeasured.** It is the one
  hot-path change slice 2 certainly needs and this spike certainly did not
  make. Everything in §3 is a measurement of hooks with `reason` left alone.
- **`HAS_THEORY = true` is unmeasured.** Every number here is the cost of
  hooks *for a theory that is compiled out*. The cost when a theory is
  actually attached — one `assert` per assigned literal, a `propagate_into`
  per fixpoint — is a different measurement and needs a real theory.
- **PHP(7,6) is 42 variables and 133 clauses.** It resolves a 6% regression,
  which is what it was used for, but a hook cost that scales with trail length
  or watch-list length would show up differently on a 100k-variable instance.
  The p4dfa arm covers that direction, but at 20 s most of it is timeouts,
  where any per-conflict cost is amortised into a budget that was going to be
  exhausted anyway.
- **The p4dfa selection is deliberate, not random** (all 6 previously-decided
  plus the 14 smallest). "Decided count unchanged" is meaningful because of
  that choice; "total time within 3%" carries the selection bias of a
  small-instance-weighted sample.
- **Host noise dominates the long instances.** `compose.s2` spans 5,955–8,903
  ms across eight runs of two nominally-identical-trajectory binaries. Any
  future p4dfa before/after at this granularity needs repeats, not single
  shots.
- **The IDL dispatch defect is not mine and not fixed.** Per the coordinator's
  profile: `dl-online` spends 18–21 s and `lia-dpll` then declines after a
  fixed ~8 s, which together exceed the 24 s budget, so **three of five traced
  IDL files are watchdog-killed before any `; theory-layer` line prints**. No
  Boolean-search improvement can be scored on those files until the dispatch
  budget is split. Slice 1 of the plan above will under-report until it is.
- **For LRA the lever is not Boolean search at all.** Per the same profile,
  the QF_LRA timeouts spend 84% of wall in `LraTheory::final_check` →
  `feasibility` → `simplex::Incremental`, at 1.3–15 ms per call over
  1,150–15,000 calls. That is simplex cost per final check — incremental
  re-solve rather than re-decide, and bound propagation to cut the number of
  calls — and neither route A nor route B touches it. Do not score LRA on
  slice 2.
- **`explain` is wired nowhere**, so the ADR-1701 soundness rule "a handle
  must stay resolvable for as long as its literal is assigned" has no
  enforcement in the native core and no test. It needs both before a theory
  emits a handle.

## 9. Artifacts

- `crates/axeyum-cnf/src/proof_sat/theory.rs` — the hook trait and `NullTheory`.
- `crates/axeyum-cnf/src/proof_sat.rs` — the generic search, the call sites,
  and `proof_sat::tests::theory_hooks`.
- `crates/axeyum-cnf/examples/native_core_sweep.rs` — the native-core-only
  DIMACS sweep used for §3.3.
- Commits: `3e0a09e4f` (design A), `925efbebc` (design B).
