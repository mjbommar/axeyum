# 09 — Coverage: what the binding reaches, what it does not, and in what order

Status: plan, 2026-08-24. Depends on plan 02. Measured basis: the generated
ledger [`docs/plan/generated/python-coverage.md`](../plan/generated/python-coverage.md)
and its artifact [`artifacts/python-coverage-v1.json`](../../artifacts/python-coverage-v1.json),
produced by `scripts/gen-python-coverage.py` from the workspace's own sources
plus the three inventories under [`inventories/`](inventories/).

Plan 02 has carried an exit criterion since it was written — *every row in the
three inventories marked tier R is bound or has a recorded reason for deferral*
— and **nothing could evaluate it**. There was no population, no join, and no
way to tell "bound" from "nobody looked". This plan supplies the ledger that
evaluates it, and the ordered slices that close what it finds.

## The measurement

```
PYTHON_COVERAGE|crates=24|public=4672|referenced=831|inventoried=250|tier_r_unreferenced=8|deferred=6
```

Read the census line, not this prose: the generated ledger is authoritative and
this document is stamped, not derived. Measured 2026-08-24.

**`referenced` is an upper bound on `bound`.** The scan sees that
`crates/axeyum-py` names an item, with comments stripped. It does not see
whether a Python callable exists, whether the wrapper is right, or whether a
test touches it. So the backlog is a *lower* bound on what is owed. The error
is pushed to the annoying side on purpose; a ledger that under-reported the gap
would be the checker-that-cannot-fail defect moved one arrow upstream.

Two holes in the join are stated rather than papered over:

- **65 inventory rows carry no tier at all** — they sit in tables with no tier
  column, under headings that name none. They are not in the backlog even
  though some are plainly read-only surface. Tiering them is an inventory edit,
  not a code change, and it belongs to whichever slice touches that table.
- **The inventories cover four crates.** `smt-solver.md`, `cas.md` and
  `kernel-kg.md` between them tier `axeyum-solver`, `axeyum-cas`,
  `axeyum-lean-kernel`, `axeyum-lean-import`, `axeyum-ir`, `axeyum-smtlib` and
  `axeyum-cnf`. **Eight crates were never inventoried at all**, so their
  tier-R count is 0 for the reason CLAUDE.md warns about: an empty answer from
  a tool nobody pointed at the subject. The slice table below is ordered by
  what those uninventoried crates are *for*, not by their tier-R count, which
  is zero by construction.

Where the gaps are (stamped copy; the generated table is authoritative):

| crate | public | referenced | unreferenced | inventoried | tier-R unreferenced |
|---|--:|--:|--:|--:|--:|
| `axeyum-solver` | 1215 | 79 | 1136 | 71 | 8 |
| `axeyum-cas` | 777 | 302 | 475 | 87 | 0 |
| `axeyum-cnf` | 357 | 29 | 328 | 7 | 0 |
| `axeyum-ir` | 346 | 240 | 106 | 20 | 0 |
| `axeyum-scenarios` | 265 | 0 | 265 | 0 | 0 |
| `axeyum-lean-kernel` | 237 | 99 | 138 | 44 | 0 |
| `axeyum-verify` | 287 | 0 | 287 | 0 | 0 |
| `axeyum-property` | 158 | 0 | 158 | 0 | 0 |
| `axeyum-search` | 151 | 0 | 151 | 0 | 0 |
| `axeyum-lean-import` | 148 | 9 | 139 | 13 | 0 |
| `axeyum-rewrite` | 129 | 0 | 129 | 0 | 0 |
| `axeyum-strings` | 110 | 0 | 110 | 0 | 0 |
| `axeyum-fp` | 73 | 27 | 46 | 0 | 0 |
| `axeyum-bv` | 55 | 9 | 46 | 0 | 0 |
| `axeyum-query` | 47 | 28 | 19 | 0 | 0 |
| `axeyum-evm` | 39 | 0 | 39 | 0 | 0 |
| `axeyum-smtlib` | 38 | 9 | 29 | 8 | 0 |
| `axeyum-egraph` | 37 | 0 | 37 | 0 | 0 |
| `axeyum-aig` | 32 | 0 | 32 | 0 | 0 |

## The slices, ordered by consumer value

A slice is one lane's PR-sized unit of work; the estimate is in **agent-slices**
of that size. Nothing here is ordered by item count — `axeyum-solver` has the
largest gap and its most valuable 133 items sit in S2, while its other ~1,000
are internal theory plumbing no Python consumer has asked for.

| # | slice | crate / modules | items | consumer | estimate |
|---|---|---|--:|---|--:|
| S1 | Read-only solver ledgers | `axeyum-solver` `backend`, `trust`, `capabilities`, `support_matrix`, `smtlib` accessors | 8 tier-R rows | the agent's route choice (plans 03, 06) | 1 |
| S2 | Lean reconstruction + receipt verifiers | `axeyum-solver::reconstruct*`, `axeyum-lean-import::verify_*` | ~143 | the flywheel's reconstruction arrow; fact-ledger evidence | 4 |
| S3 | Combinatorial search | `axeyum-search` (`cover`, `colouring`, `vdw`, `offdiag`, `ledger`, `certify`) | 151 | the 104 committed claims in `artifacts/claims/{rado,offdiag-schur,vdw}` | 3 |
| S4 | CNF proof machinery | `axeyum-cnf` `lrat`, `drat_resource`, `xor_matrix`, `gf2`, `bve`, `interpolant`, `cube`, `alethe` | ~160 | Lean-parity: every `unsat` carries a checkable proof | 2 |
| S5 | CAS number theory and combinatorics | `axeyum-cas` `ntheory{,_more,_advanced}`, `combinatorics`, `permutation`, `orthopoly`, `special`, `hyperbolic`, `boolean`, `linear_elim`, `cofactor_ansatz`, `gf2_search`, `gf2_extension` | ~180 | autogenesis producers; `math-education` concept coverage | 3 |
| S6 | Rewriting | `axeyum-rewrite` (`canonical`, `arrays`, `solve_eqs`, `int_blast`, `quantifiers`) | 129 | Python query pipelines; QF_ABV via `eliminate_arrays` (ADR-0010) | 2 |
| S7 | String reasoning | `axeyum-strings` `solve_word_equations`, `refute_word_equations`, `regex`, `classes`, `infer` | 110 | string-route diagnosis; ADR-0052 gate work | 2 |
| S8 | Progress sinks | `axeyum-solver::{ProofProgress,CheckProgress}`, `axeyum-cnf::ProofSearchProgress` | 4 | long runs in a notebook; the agent's liveness signal | 1 |
| S9 | OMT | `axeyum-solver::optimize_smtlib{,_lexicographic}` + the upstream budget fix | 2 + fix | optimisation queries from Python | 1 |
| S10 | E-graphs | `axeyum-egraph` | 37 | rewriting/e-matching experiments | 1 |

### S1 — read-only solver ledgers (1 slice)

**Binds** the entire current backlog, all of it tier R and all of it in
`axeyum-solver`: `solve_smtlib_get_assertions` / `_get_info` / `_get_option`
(`smtlib.rs:2380/2451/2524`), `SolveStats` (`backend.rs:595`), `Capabilities`
(`backend.rs:613`), `TrustId`/`TrustStep` (`trust.rs:26`),
`Assurance`/`Capability`/`CheckedBy` (`capabilities.rs:26`), and the five
`support_matrix.rs:36` status types behind `support_matrix()`.

**Consumer.** Plan 03's agent picks a route, and plan 06 turns typed declines
into an obstruction graph; both need to read *what this build can do* rather
than infer it from a failure. `trust_ledger()` is also the honest answer to
"how much of this verdict is checked" — data the Python layer must not
paraphrase.

**Hazards.** None of substance: every type here is owned plain data
(inventory §6 lists the complete `Send`/`Sync`/lifetime exception set, and none
of these is in it). `SolveStats` holds `Duration`s — expose seconds as `float`
*and* the raw nanoseconds, since a benchmark that silently rounds is worse than
one that is awkward.

**Tests.** Differential against the shipped binaries, which need no cargo lock:
`target/release/examples/` carries the support-matrix and trust-ledger dumpers;
the Python rendering must be byte-equal to `trust_ledger_markdown()` on the
same build. Assert a nonzero row count in each.

### S2 — Lean reconstruction and receipt verifiers (4 slices)

**Binds** `axeyum-solver`'s `reconstruct*` modules (112 public items under
`reconstruct/`, 133 including `int_reconstruct`, `lex_reconstruct`,
`word_reconstruct`, `regex_reconstruct`), `membership_unsat_lean_module` /
`membership_unsat_certificate`, and the `verify_*` half of
`axeyum-lean-import`'s receipts (10 public verifiers).

**Consumer.** This is the flywheel's third arrow — reconstruction → kernel term
→ admitted, axiom-free. Everything the autogenesis lanes do by hand through
example binaries becomes scriptable, and an agent that produces a proof can
check it in the same process.

**Hazards.** The verifiers are the reason this is four slices and not one. A
certificate must carry every distinction its producer makes; a Python caller
holding only a verifier can accept a receipt shape the issuer never emits, and
`issue_*` therefore stays Rust-side until the receipt shapes freeze (plan
02-D). Every route must round-trip through the kernel: the acceptance test is
`axiom_footprint` measured **from the kernel**, never read from source text
(CLAUDE.md, and `nat_theorem_inventory` exists because three counts of this
repository's theorems were wrong before anyone built the environment to look).

**Tests.** Per route: reconstruct in Python, admit into a second `Kernel`, and
assert the footprint is empty; one tampered proof term per route is
**rejected** — a checker that has never been shown to fail is not a checker.
Cross-check `canonical_declaration_sha256` against the committed
`*-result-v1.json` for each settled family fact.

### S3 — combinatorial search (3 slices)

**Binds** `axeyum-search`: `cover` (51), `colouring` (25), `harness` (23),
`ledger` (15), `vdw` (13), `offdiag` (10), `family` (8), `certify`, `compose`.

**Consumer.** The claim ledger. `artifacts/claims/` has three families — `rado`,
`offdiag-schur`, `vdw` — and this crate is what produced them
(`crates/axeyum-search/{tests,examples}` are the current drivers). Binding it
lets `validate-claims.py`'s subjects be *re-derived* from Python rather than
re-read, which is the difference between a dashboard and a check.

**Hazards.** `harness.rs` and `ledger.rs` write files; the binding exposes them
behind an explicit opt-in, the way plan 02-B treats GF(2) shard directories.
Long searches need S8's progress route or a documented "this blocks" note —
not a silent one.

**Tests.** Reproduce one settled claim per family end to end and compare the
certificate hash with the committed `claim.json`; assert a nonzero comparison
count. Negative control: a perturbed cover must be **rejected** by
`certify`.

### S4 — CNF proof machinery (2 slices)

**Binds** `axeyum-cnf` beyond the 29 items already reached: `lrat` (10),
`drat_resource` (58), `xor_matrix` (10), `gf2` (14), `bve` (8), `interpolant`
(10), `cube` (14), `alethe` (13), `vivify`/`compact` (12).

**Consumer.** Lean parity is *every unsat carries a machine-checkable proof*.
`check-claim-certificates.py` shells out to `drat-trim`; a Python caller that
can build the CNF, get the DRAT/LRAT and re-check it in-process closes that
loop without a third-party binary on the host.

**Hazards.** `DratCheckOutcome::ResourceOut` is neither `True` nor `False` and
must not collapse to `bool` (plan 02-A). `drat_resource`'s budgets are the
difference between "refuted" and "gave up": expose the counts, not a verdict.

**Tests.** Every route re-checks a committed proof and **rejects** a mutated
one; `recheck_lrat()` returns `None` on a DRAT-only proof, never `False`.

### S5 — CAS number theory, combinatorics, transforms and normal forms (3 slices)

**Binds** the unreferenced 475 of `axeyum-cas`, prioritised: `ntheory` (15),
`ntheory_more` (21), `ntheory_advanced` (14), `combinatorics` (21),
`permutation` (12), `boolean` (21), `orthopoly` (8), `special` (6),
`hyperbolic` (9), `algebraic` (8), `linear_elim` (6), `cofactor_ansatz` (5),
`gf2_search` (4), `gf2_extension` (25), plus tiering the 8 untiered `cas.md`
rows as the slice touches them.

**Consumer.** The autogenesis producers and the `math-education` concept graph:
these are the functions a proposer needs to *compute* with before it can
propose. `cofactor_ansatz` and `linear_elim` are the ones the Gröbner
certificate route calls when the budgeted path declines.

**Hazards.** `Option::None` means overflow or outside-the-fragment, never
error, across the whole crate (plan 02-B) — and it is the single easiest thing
to turn into an exception by reflex. `CasExpr::rat(n, 0)` panics; wrap in
`checked_new`. `sets::Interval` collides with `interval_arith::Interval` and is
exposed as `cas.RealInterval`.

**Tests.** Cross-check against `fractions`/`math` on random inputs with an
asserted comparison count; every partial operator exercised **with its
degenerate argument** (the fuzz-seed-class hard rule applies to the binding's
tests too).

### S6 — rewriting (2 slices)

**Binds** `axeyum-rewrite`: `canonical` (34), `arrays` (14, including
`eliminate_arrays`), `functions` (14), `int_blast` (9), `solve_eqs` (9),
`quantifiers` (7), `reconstruct` (7), `elim_unconstrained`,
`propagate_values`, `alpha`.

**Consumer.** Anyone building a query in `axeyum.ir` and wanting it smaller
before it is solved, and QF_ABV via read-over-write + Ackermann (ADR-0010).
The canonicalizer is denotation-preserving, which makes it the one preprocessing
step a Python caller can apply without changing the answer — and the one whose
*failure* to preserve denotation a test can catch.

**Hazards.** Every rewrite is denotation-preserving by contract, so the test is
not "did it get smaller" but "does it decide the same": bind the manifest
contracts alongside the rewrites, never the rewrites alone.

**Tests.** For ≥ 20 corpus files, `solve(rewrite(q)) == solve(q)`, count
asserted; `eliminate_arrays` differential against
`check_with_array_elimination` on the committed QF_ABV corpus.

### S7 — string reasoning (2 slices)

**Binds** `axeyum-strings`: `solve_word_equations`, `refute_word_equations`,
`RefuteOutcome`, `regex` (58), `classes` (17), `infer` (12), `arrange` (8),
`lex_order` (6), `check_derivation` (5), `normal_form`, `refute`.

**Consumer.** String-route diagnosis. The `explain_corpus` gotcha in CLAUDE.md
exists because the flat view and the front door disagree on 134 of 397
benchmarks; a Python caller that can drive the word/regex layers directly is
how that gets measured rather than argued about.

**Hazards.** The front-door string routes in `axeyum-solver` take
`&mut Script` and are **deferred** (see the ledger) — this slice binds the
`axeyum-strings` crate, which is plain owned data, not the solver's route
selection. Do not let the two blur: a Python caller must not be able to build a
second, weaker front door.

**Tests.** The oracle-free `:status` corpus sweep is the pre-merge gate for any
string-route change; the Python tests mirror it with an asserted file count,
and the generators cover the full SMT-LIB literal grammar including
`\u{...}` escapes and code points above `0xFF` (a wrong-verdict class hid for
weeks behind generators that omitted exactly that).

### S8 — progress sinks (1 slice)

**Binds** `ProofProgress`, `CheckProgress`, `CheckingProgress`,
`ProofSearchProgress` as a background-thread iterator.

**Consumer.** A notebook or an agent watching a long solve. Today the only
signal is "still running".

**Hazards.** These four are why `SolverConfig` is `Send` but `!Sync`
(inventory §6): binding them means owning a Rust thread and draining an
`mpsc::Receiver` from Python, with a documented shutdown. `SolverConfig` stops
being a trivially clonable `#[pyclass]` the moment they are attached — which is
exactly why v1 omits them and this is a slice of its own.

**Tests.** A run that emits ≥ 2 progress records, asserted; a dropped iterator
must not leak the thread (checked by thread count before/after).

### S9 — OMT (1 slice)

**Binds** `optimize_smtlib` and `optimize_smtlib_lexicographic` — *after* the
upstream fix. Both currently ignore `config` (`let _ = config;`,
`smtlib.rs:2091/2119`), so binding them first would advertise timeouts, node
budgets and memory limits that do not apply. A budget that cannot bite is worse
than no budget, because the caller stops watching.

**Tests.** The budget must be shown to bite: a query that exceeds the node
budget returns `unknown` with `kind == "NodeBudget"`, not an answer.

### S10 — e-graphs (1 slice)

**Binds** `axeyum-egraph` (37 items, one module). Small, self-contained, no
consumer is blocked on it — which is why it is last rather than absent.

## Do not bind

Not a backlog. These have reasons, and a lane that binds one anyway should
change this list first.

| subject | reason |
|---|---|
| `axeyum-verify`, `axeyum-verify-macros` (292) | Test-time infrastructure and proc macros. A `#[proc_macro]` expands at Rust compile time and has no runtime form to project; the property harness's value is that it runs *inside* `cargo test`. |
| `axeyum-property`, `axeyum-property-macros` (159) | Same: generators and shrinkers driven by the Rust test harness. A Python re-implementation would be a second, weaker generator — and the fuzz-seed-class rule says the generator is where soundness lives. |
| `axeyum-bench` (0 public items) | A binary harness. Its output is JSON artifacts, which `axeyum.knowledge` already reads; there is nothing to call. |
| `axeyum-scenarios` (265) | Self-checking consumer workloads for testing and optimisation (ADR-0008). They exist to be *run by the gates*; a Python caller wanting one should read the artifact. |
| `axeyum-evm` (39) | No consumer. Revisit if a Python symbolic-execution user appears — and then inventory it first, because it has never been tiered. |
| `axeyum-wasm` (2) | A different binding of the same core, for a different host. Two bindings of one crate is the design; binding one from the other is not. |
| `axeyum-aig` (32) | Reachable through `axeyum.ir`'s lowering already (`Aig.to_aiger_ascii` is in plan 02-A). The rest is circuit-internal. |
| the items in `artifacts/python-coverage-deferrals.json` | 30 entries, each with a reason: borrowing types (`CheckBudget<'a>`, `QueryBuilder<'a>`), consuming APIs (`into_parts`), one-way kernel operations, unbudgeted search, `&mut Script` front-door internals, and `checked_flat_view` — whose empty assertion list on a word-first-fallback parse solves as a vacuous `sat`, a shipped P0. |

## Exit criteria for this plan

- `python3 scripts/gen-python-coverage.py --check` is green, and it runs in
  `scripts/check.sh` and `just check`. A stale ledger is a failed gate.
- Every tier-R inventory row is referenced **or** carries an entry in
  `artifacts/python-coverage-deferrals.json` with a non-empty reason:
  `tier_r_unreferenced=0` in the census line. This is plan 02's exit criterion,
  now with something that can evaluate it.
- The 65 untiered inventory rows are tiered, so the join has no silent hole.
- Every crate in the "do not bind" table above still has a reason, and the
  reason is checked when it changes: a crate that acquires a Python consumer
  moves to a slice, it does not stay on the list.
- `python3 scripts/tests/mutation_controls.py python-coverage` reports every
  mutation as `killed N`.
