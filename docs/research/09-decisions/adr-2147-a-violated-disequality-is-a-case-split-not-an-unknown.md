# ADR-2147: a disequality the candidate model violates is a case split, not an `unknown`

Status: accepted
Index-summary: The LRA-MODEL-REPLAY census found 11 pinned `QF_LRA` files losing their verdict to ONE dropped case -- `LraTheory::assert` turns an equality atom asserted FALSE into nothing (`lra_online.rs`, `(AtomKind::Equality { .. }, false) => Vec::new()`) under a comment that said the driver never sets one; true of the offline driver it named, false of the CDCL(T) driver, whose `is_lra_atom` admits every real `Op::Eq`. Sized at head with the shipped route's own probe: `sc-25` has **371 of 776** equality atoms false at the moment the witness is read out (the census's number exactly), 8 of them violated by the point. The repair is cvc5's shape (`splitDisequalities`, `theory_arith_private.cpp:4251-4286`): at a FEASIBLE complete check, evaluate each false equality at the point and, for one on its hyperplane, register `e < c` and `e > c` as fresh atoms -- once per equality, ever -- riding the equality's OWN two tableau rows at the strict relation, so no row is added mid-search and none is ever bounded twice; the three trichotomy edges `{eq,lt}`, `{eq,gt}`, `{lt,gt}` fall out of the existing form-bound crossing at `assert`, and `{~eq,~lt,~gt}` is the one new conflict, at the next complete check. The native core polls `take_new_atoms` once more after a `Sat` final check, because the point exists only there. TWO defects found on the way: the ADR-1704 artifact constructor PANICKED on a lemma over a fresh variable (`TheoryRefutation::from_cnf_and_lemmas`, widened), and the shipped route cannot refute `x != y, x <= y, x >= y` at all (`unknown`, not `unsat`). Smoke on the census family: `sc-7` unknown@24 s -> **unsat in 0.6 s** (23 splits, 15 trichotomy conflicts), `sc-9/11/13/15/17` all `unsat` under 21 s, `sc-19..25` and `pursuit-safety-16` still `unknown` -- the split turns a wall into a search that does not finish. A/B: pinned 107 -> 113 (5 STABLE-GAIN + 1 UNSTABLE after 3x recheck), held-out 93 -> 97, QF_UFLRA 148 -> 150 (2 stable), QF_IDL/QF_RDL unmoved, 0 losses, 0 flips, 0 `:status` disagreements, 0 aborts. **SHIPS ON.**
Index-status: accepted
Date: 2026-09-17

## Context

[ADR-2045](adr-2045-the-bound-is-not-the-wall-qf-lra-is-one-offline-dense-engine.md)
named "online CDCL(T) LRA model did not replay (arithmetic outside the
incremental engine)" as the capability wall of the `QF_LRA` division, and
[ADR-2111](adr-2111-qf-lra-what-the-same-simplex-does-differently.md) sized
the largest addressable bucket behind it. The LRA-MODEL-REPLAY census
([`bench-results/lra-model-replay-20260916/`](../../../bench-results/lra-model-replay-20260916/README.md))
then read the sentence against the engine's own atom classification and
refuted its subject: across the 47 undecided files that end there, the number
of atoms the engine could not represent is **zero**. Three mechanisms hide
behind the one string, and this ADR takes the one that is a construct:

> the model **was** built, the failing assertions evaluate to `false`, and the
> only offending atoms inside them are real equalities the SAT solver asserted
> **false**.

Eleven of the pinned 200 lose their verdict to it (the `sc-7 … sc-25` family
and `sal/pursuit/pursuit-safety-16`); five more (`clocksynchro_{2,4,6,8}`,
`sc-5`) hit the identical wall and are rescued by a later route.
[ADR-2146](adr-2146-the-online-tableau-is-admitted-on-the-currency-it-is-stored-in.md)
takes the second mechanism; the third (a timeout wearing an incompleteness
label) is not in this lane's scope.

## Sizing at head

The census measured at `4f81de9c1`; main is ~120 commits on. Re-run with the
shipped `smtcomp_cli` at `43f1e0f90` (sha256 `d3606850…`, the same bytes
ADR-2134's held-out lane built), 24 s / 8 GiB / one pinned core, `--trace` +
`AXEYUM_LRAMODELPROBE=1`, at both the shipped screen and the census's
`AXEYUM_LRA_ATOM_SCREEN=16`
([`bench-results/lra-admission-diseq-20260917/sizing-summary.txt`](../../../bench-results/lra-admission-diseq-20260917/sizing-summary.txt)):
**11 of 11** stop at `model-built-but-does-not-replay`, at both screens, all
`unknown`, all exit 0. The mechanism is where the census left it.

The disequality count is confirmed **from the shipped route itself**, not
from a patched tree: the lever binary's OFF arm prints, at the moment the
witness is read out, how many equality atoms the search set false and how
many of those the point violates (`LraTheory::model`, under
`AXEYUM_LRAMODELPROBE=1`; `sizing-wip-off-diseq11.tsv`):

| file | equality atoms | asserted FALSE | violated by the point |
|---|---:|---:|---:|
| `sc-7.base.cvc` | 218 | 103 | 9 |
| `sc-9.base.cvc` | 280 | 135 | 4 |
| `sc-11.base.cvc` | 342 | 162 | 3 |
| `sc-13.base.cvc` | 404 | 192 | 12 |
| `sc-15.base.cvc` | 466 | 224 | 8 |
| `sc-17.base.cvc` | 528 | 254 | 11 |
| `sc-19.base.cvc` | 590 | 282 | 9 |
| `sc-21.base.cvc` | 652 | 308 | 9 |
| `sc-23.base.cvc` | 714 | 341 | 16 |
| **`sc-25.base.cvc`** | **776** | **371** | 8 |
| `pursuit-safety-16` | 650 | 392 | 69 |

The 776 / 371 on `sc-25` is the census's number exactly. The third column is
the new one: the wall is never more than a few dozen atoms wide, because a
disequality the point already satisfies costs nothing — the same relevancy
the replay gate has, and the reason a split is cheap.

## What each side does today, at `file:line`

### axeyum, before this ADR

`LraTheory::assert` (`crates/axeyum-solver/src/lra_online.rs`):

```rust
// Equality-false (disjunction) and unsupported atoms add nothing.
(AtomKind::Equality { .. }, false) | (AtomKind::Unsupported, _) => Vec::new(),
```

with the doc comment "the driver only ever sets equality atoms *true* anyway,
since `check_qf_lra_online` does not abstract bare equalities". That is true
of the offline `Dpll` driver it names. The CDCL(T) route
(`lra_theory.rs::check_qf_lra_online_cdclt`) collects atoms with
`is_lra_atom`, which admits any real `Op::Eq`, gives every one a skeleton
variable, and the native core sets it either way. The theory records the
assignment and adds no constraint; the simplex answers `Feasible` over a
system strictly weaker than the assignment; `real_model()` materializes the
point; `replays` rejects it; the route answers `unknown` with the sentence
above. The same drop is repeated at the cube decider (`cube_check`), the
propagation validity check and the eager-mode propagator, none of which this
ADR touches: they never see a split atom.

### z3: eager

`theory_lra::new_diseq_eh` → `arith_eq_adapter::mk_axioms`
(`references/z3/src/smt/arith_eq_adapter.cpp:163-178`, the axioms at
`:208-210`): at internalization of `t1 = t2` the adapter creates the two bound
atoms `t1 ≤ t2` and `t1 ≥ t2` and asserts three "triangle-eq" theory axioms
`¬eq ∨ le`, `¬eq ∨ ge`, `eq ∨ ¬le ∨ ¬ge`. The SAT solver does the case split;
the LP never sees a disequality. Every equality pays two atoms and three
clauses whether or not the search ever falsifies it. The old `theory_arith`
says why the simplex core has no disequality handling: "Starting at Z3 V2.0,
we split disequalities. So, we do not need to handle them."
(`theory_arith_core.h:3146-3148`).

### cvc5: lazy, model-driven

`TheoryArithPrivate::splitDisequalities`
(`references/cvc5/src/theory/arith/linear/theory_arith_private.cpp:4251-4286`):
disequalities wait in `d_diseqQueue`; at full effort each is compared against
the `DeltaRational` assignment and, **only when the assignment sits on the
hyperplane**, `Constraint::split` (`constraint.cpp:1265-1286`) emits the lemma
`(or (<= x y) (>= x y))` — a tautology whose two atoms cvc5's constraint
database then combines with the standing `≠` into the strict bounds. A
disequality the assignment already satisfies costs one comparison and no
lemma.

### The near shape, and what is different here

cvc5's is the near one: **we already detect the violation** — that is
precisely what the `replays` gate does — and turned it into `unknown` instead
of into a lemma and a continued search. Two things differ in the port:

1. The lemma is over **strict** atoms. cvc5 derives `<` from `≤ ∧ ≠` inside
   its constraint database; our theory has no such derivation, so the halves
   are registered as `e < c` and `e > c` directly and the disjunction is the
   trichotomy `eq ∨ lt ∨ gt`.
2. The halves ride the equality's **own rows**. The warm tableau is built once
   at construction and a row holds ONE bound at a time
   (`SimplexEngine::sync` refuses a second). An equality already has two rows
   — `e ≤ c` and `−e ≤ −c` — and the strict halves are those two rows at
   `Rel::Lt`. So no row is added mid-search; what has to be guaranteed is that
   no row is ever bounded twice, and that is exactly what the three triangle
   conflicts do, at `assert`, before any `sync`.

## The change

All behind `AXEYUM_LRA_DISEQ_SPLIT` (`1` | `on`; anything else, the empty
string included, is OFF — the ADR-2125 rule), read once per process, with the
arm also passable as a value (`LraOnlineLevers`,
`check_qf_lra_online_cdclt_with_levers`) so one process can run both.

1. **`AtomKind::Split { when_true }`** (`lra_online.rs`): a strict half.
   Asserted true it imposes `when_true` (the equality's row at `Lt`);
   asserted **false it imposes nothing**. That is complete, not lossy: with the
   three triangle conflicts in force, `¬lt` is entailed by whichever of `eq`
   / `gt` is true whenever the assignment is total, and a partial assignment
   is never handed to a complete check.
2. **`LraTheory::split_violated_disequalities`**: after `feasibility()` has
   answered `Sat` at a complete check, read the point from the engine the
   check just ran on (the same point `model` will materialize for the replay),
   walk every equality atom asserted false, evaluate its functional in
   checked arithmetic, and for each on the hyperplane either register the two
   halves (once per equality, ever; `split_of`), or — if the halves exist and
   the assignment set both false — answer the conflict `{¬eq, ¬lt, ¬gt}`.
   Every literal in that core is asserted, so the clause the driver learns is
   `eq ∨ lt ∨ gt`, an LRA tautology. No engine (the Fourier–Motzkin fallback)
   or a point outside `i128` means no split: the route then behaves as it did.
3. **The other two triangle edges are not new code.** `install_bounds`
   (ADR-1701's cheap partial check, generalized to forms by S4) already tracks
   the tightest bound per linear form per side with strictness; `e < c`
   against `e = c` is an upper bound at `c` strict against a lower bound at
   `c`, and `bound_crossing` answers `{eq, lt}` in either assertion order;
   `{lt, gt}` likewise. `a_strict_half_against_its_equality_conflicts_at_assert`
   pins all three orders.
4. **`TheorySolver::take_new_atoms`** is implemented (it defaulted to 0), and
   `CdcltLraTheory` forwards it — without the forwarder the arm is inert
   while looking armed, ADR-2125's own failure shape, and a mutation control
   pins exactly that.
5. **The native core re-polls after a `Sat` final check**
   (`axeyum-cnf/src/proof_sat.rs`): the fixpoint poll in `theory_round` runs
   BEFORE the complete check, and the halves are discovered AT it, because
   the violated hyperplane is a property of the feasible point and the point
   exists only there. Fresh atoms re-open the assignment, are decided at the
   route's initial phase (true first: a half is useful true), and the loop
   reaches a complete check again. A theory that registers nothing takes the
   branch it always took. Bounded: each equality splits once.

Scoped to the deferred mode (`with_diseq_split` panics otherwise): the eager
mode has no complete check to split in, and the offline `Dpll`, the
`uflra_online` combination loop and the cube decider never enable it, so they
are byte-identical — which is what the `QF_UFLRA` arm of the A/B is for.

## The certificate route

An `unsat` from this route is the ADR-1704 two-stream artifact — the CNF, the
enumerated theory lemmas, and a DRAT stream over `cnf ++ lemmas` — graded
`SatRefutationModuloTheory` and never certified, because every Farkas core the
theory ever contributed is a lemma the checker takes on trust. The split's
clauses are theory lemmas of exactly that kind, in the same list, read by the
same checker; the grade does not move. What DID move is that the halves are
variables the CNF never declared, and `TheoryRefutation::from_cnf_and_lemmas`
sized the extended formula at the CNF's count and **panicked** on the first
such lemma, on the stated grounds that "no producer in this crate can do" it.
The extended formula is now widened to the widest lemma variable; the lemma
list still says which clauses are trusted; `check()` answers
`CheckedModuloLemmas`.
`an_unsat_after_a_split_lemma_still_carries_the_two_stream_artifact` pins
this on `x ≠ y ∧ x ≤ y ∧ x ≥ y`, and its mutation (un-widening) kills exactly
that test. So: an `unsat` that follows a split lemma carries what it carried
before, and nothing is withheld.

## The controls

Unit, in `lra_online::tests` (theory level) and `lra_theory::tests` (through
the route, both arms in one process):

* `a_violated_disequality_registers_its_two_strict_halves_once` — the
  registration, once, drained by one poll;
* `both_halves_false_is_the_trichotomy_conflict_and_a_true_half_is_a_model` —
  the new conflict is exactly the three asserted literals, and the `x < y`
  branch has a witness that replays `x ≠ y`;
* `a_strict_half_against_its_equality_conflicts_at_assert` — `{eq,lt}` in
  both orders, `{lt,gt}`, and the SATISFIABLE neighbour (eq true, both halves
  false);
* `with_the_split_off_a_violated_disequality_registers_nothing` — the OFF arm
  registers nothing, and the origin does NOT satisfy `x ≠ y` (the wall);
* `a_disequality_the_point_satisfies_is_not_split` — relevancy by the point;
* `the_split_refuses_the_eager_mode`;
* `a_bare_disequality_is_unknown_shipped_and_sat_split` — the 11-file wall in
  one line: `unknown` at the replay gate shipped, `sat` with a replaying
  witness split;
* **soundness-negative, `unsat` side**:
  `a_split_never_manufactures_a_model_for_an_infeasible_disequality` —
  `x ≠ y ∧ x ≤ y ∧ x ≥ y` is `unsat` under the split (and, a finding in its
  own right, `unknown` shipped: the route cannot refute it at all today);
* **soundness-negative, `sat` side**:
  `a_split_lemma_must_keep_the_equality_or_it_refutes_a_satisfiable_query` —
  `(x = y) ∨ (x ≠ y ∧ x < 0 ∧ x > 0)` has the one model `x = y`; a split whose
  learned clause dropped `eq` would refute it;
* `three_mutual_disequalities_are_decided_by_backtracking_over_the_halves`;
* `an_unsat_after_a_split_lemma_still_carries_the_two_stream_artifact`;
* `the_lever_spellings_and_the_default_are_off`.

Fuzz seed classes (the hard rule: a partial or dropped case must be
GENERATED): `qf_lra_differential_fuzz` now emits `distinct` over 2..=all of
an instance's variables on a third of the seeds (lowered to the pairwise
`(not (= vᵢ vⱼ))` the parser produces, and to z3's own `distinct`), and its
coverage guard requires ≥ 400 disequalities, ≥ 300 instances carrying a
`distinct` and ≥ 600 pairwise disequalities over the 1,500 seeds (measured
898 / 488 / 1,043). The five LRA/DL/LIA z3 fuzzes run in all four env arms.

Mutation controls (`scripts/tests/mutation_controls.py`, one test per suite
so a kill names exactly one test): `lra-diseq-split-registers` (four
mutations, each making the arm inert at a different site: the theory's
registration, the point evaluation, the adapter's forwarder, the core's
re-poll), `lra-diseq-split-keeps-eq` (the core drops `eq`),
`lra-diseq-split-strict-half-binds` (a true half imposes nothing),
`lra-diseq-split-artifact` (the extended formula is not widened).

## The measurement

One binary (`smtcomp_cli`, `--release --features full`, sha256
`8079669575dc…`), env arms interleaved per file on the same pinned core with
the arm order rotating per file, 24 s / 8 GiB `ulimit -v`, `$EPOCHREALTIME`
timing (200 ms self-check 203–204 ms), hosts s5 and s6 idle at launch
(`bench-results/lra-admission-diseq-20260917/`, `ab/` for every row).
Four arms: `base` (nothing set), `nz` (ADR-2146), `sp` (this lever), `both`.

| population | base | `sp` | `both` | gains | losses | flips | `:status` disagreements | rc-134 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `QF_LRA` pinned 200 | **107** | **113** | 113 | 6 (`sc-7/9/11/13/15/17`, all `unsat` = `:status`) | 0 | 0 | 0 | 0 in every arm |
| `QF_LRA` held-out 200 (ADR-2132's draw, disjoint) | **93** | **97** | 97 | 4 (`uart-8.base` unsat; `sc-10.induction2`, `sc-15.induction2`, `sc-18.induction` sat) | 0 | 0 | 0 | 0 |
| `QF_UFLRA` pinned 200 | **148** | **150** | 150 | 2 (`cpachecker-induction … minepump_spec{3,4}`, unsat) | 0 | 0 | 0 | 0 |
| `QF_IDL` pinned 200 (control, `base` / `both`) | 112 | — | 112 | 0 | 0 | 0 | 0 | 0 |
| `QF_RDL` pinned 200 (control, `base` / `both`) | 150 | — | 150 | 0 | 0 | 0 | 0 | 0 |

`base` re-derives the board's 107 exactly. Wall on the pinned 200 fell
2,281 → 2,173 s (the six files that used to burn 24 s each now decide in
0.5–20 s). The `sc` gains carry `diseq_splits` in the trace (sc-7: 23 splits,
15 trichotomy conflicts, 0.6 s).

**3× rechecks** (`recheck-movers-env.sh`, three passes per arm, arms
alternating within the passes, one binary, `-` against
`AXEYUM_LRA_DISEQ_SPLIT=1`):

| population | STABLE-GAIN | STABLE-LOSS | UNSTABLE |
|---|---:|---:|---:|
| `QF_LRA` pinned | **5** (`sc-7/9/11/13/15`) | 0 | 1 (`sc-17`: `unsat` 2/3, decided at 19–20 s of 24) |
| `QF_LRA` held-out | **4** (`uart-8.base`, `sc-10.induction2`, `sc-15.induction2`, `sc-18.induction`) | 0 | 0 |
| `QF_UFLRA` pinned | **2** | 0 | 0 |

The same rows rechecked `-` against `both` classify identically (the nonzero
admission is inert at the shipped screen, ADR-2146).

**Ship criterion** (0 stable losses, 0 flips, 0 `:status` disagreements,
≥ 1 stable gain on pinned AND held-out, no new abort): **met** — 5 stable
pinned gains, 4 stable held-out gains, 2 stable `QF_UFLRA` gains,
0 losses of any kind, 0 flips, 0 disagreements over every decided row, 0
aborts in any arm, both DL controls unmoved. **The split ships ON**:
`AXEYUM_LRA_DISEQ_SPLIT` is read with `parse_lever_default_on` (`0` | `off`
disarms it, anything else is ON), `LraOnlineLevers::shipped()` carries it,
`LraOnlineLevers::off()` is the pre-ADR route every fixture compares against,
and `the_shipped_route_decides_a_bare_disequality` is the default-carrying
test (ADR-2140's shape: exactly it dies on a moved default).

What the split does NOT buy, measured: the larger `sc-19 … sc-25` and
`pursuit-safety-16` (the other 5 of the census's 11) still time out — the
wall is gone and the search that replaces it does not finish in 24 s. Under
`AXEYUM_LRA_ATOM_SCREEN=16` (ADR-2146's composition table) the same six
`sc` files are the only gains.

## Gates run

Every count nonzero, read from the `test result:` line
(`/data0/axeyum-lane-scratch/a13-lra/gates*/`):

* the five z3 differential fuzzes — `qf_lra_differential_fuzz` (8),
  `simplex_lra_fallback_differential` (1), `qf_uflra_differential_fuzz` (2),
  `difference_logic_differential_fuzz` (4), `qf_lia_differential_fuzz` (5) —
  in all four env arms before the flip (20 runs, exit 0) and again after it
  (unset = ON, `off`, `nz`, `nz`+`off`): 20 runs, exit 0, the same counts; the QF_LRA fuzz with `--nocapture` reads **1,500 / 1,500 agree, 0 unknown, 0 disagree** and the boundary class **12 / 12 agree** in both admission arms;
* `corpus_regression --features full`: 2 passed (before and after the flip);
* `--lib --features full lra`: 162 passed, in three arms; `simplex`: 43;
* the full solver lib sweep the push hook runs (`--skip reconstruct::`,
  4 threads): 1,679 / 1,680 with the one red
  (`euf_egraph::…_is_bounded_by_timeout`) load-sensitive — it failed twice
  under other lanes' load of 55–105 and passed alone at load 1.4 (292 s);
  every other theory's `take_new_atoms` is 0, so the re-poll is a no-op on
  that route; post-flip, quiet box: **1,681 passed, 0 failed**;
* `axeyum-cnf --lib`: 645 passed;
* `lia_online` (9), `lra_online` (9, in three arms), `cdclt_lra_online` (10),
  `cdclt_lia_online` (10), `lra_warm_screen_2132` (3), `lra` (20),
  post-flip also `uflra_online` (21) and `uflia_online` (33: 32 + `opaque_app_interface_overflow_declines_without_enumerative_fallback`, which fails identically with the split OFF and fails the same way at the merge base `43f1e0f90` in a `lane-snapshot.sh` tree: pre-existing on main, not this diff);
* workspace `clippy --all-targets --all-features -D warnings`: exit 0;
  `cargo check --workspace --all-targets`: clean; `cargo fmt --all --check`:
  clean; `check-config-registry-staleness.py`: 0 unexplained;
  `check-suite-gating.py`: PASS; `check-lcg-raw-state.py`: PASS;
  `check-merge-hygiene.sh`: PASS; `check-links.sh`: all links ok;
* mutation controls: nine suites, every mutation `killed 1` naming its one
  test, `--check-anchors` stale=0 — after ONE finding: the first sat-side
  fixture SURVIVED the eq-dropping mutation (the search decided `eq` true
  first and never split), and was replaced by one whose first branch is the
  split (§controls);
* `progress_frontier --features full -- --test-threads=1` on `taskset -c 0-7`,
  box at load 3: **12 passed, 0 REGRESSION** (baselines re-calibrated by the
  run and restored, not committed).

## Consequences

* The comment at the drop site is corrected: the case arises, and the census
  numbers are written where the next reader will see them.
* `TheoryRefutation::from_cnf_and_lemmas` no longer panics on a lemma over a
  fresh variable, for every theory that registers atoms mid-search, not only
  this one.
* A theory's `Sat` at a complete check is no longer necessarily a verdict:
  the core asks once more whether the theory registered something. A theory
  that registers forever would spin; this one splits each equality once.
* The trace carries `diseq_splits` and `diseq_split_conflicts`, so an arm
  that decides nothing can be told from an arm that never ran.
