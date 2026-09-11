# B3: `qinst_egraph` on the native core — the adapter defect is a wrong verdict, the migration is invariant, and two of the plan's facts were wrong

**Lane:** E5 (`E5-qinst-migrate`), 2026-09-10.
**Phase:** B3 of
[the CDCL consolidation plan](../../solver-comparison-2026-09/12-cdcl-consolidation-plan.md),
under [ADR-1908](../09-decisions/adr-1908-the-native-core-is-the-one-cdclt-driver-cdclt-is-demoted-to-an-oracle.md),
after [ADR-1909](../09-decisions/adr-1909-warm-cdclt-is-one-theory-push-pop-scope-per-solve.md).
**Decision recorded as:**
[ADR-1911](../09-decisions/adr-1911-a-warm-cdclt-driver-reports-its-variable-count-and-owns-its-theory.md).
**Commits:** `5c2e6a818` (the adapter fix and its guard), and the migration
commit that carries this note.

Two pieces of work, and the first one is a latent wrong answer.

---

## 1. The mirrored counter: a wrong verdict, and the `debug_assert` does not fire

`NativeTheoryAdapter` kept a private `next_var`, seeded from the
construction-time variable count and bumped once per registered atom.
[E3's note](warm-cdclt-native-2026-09-10.md) §5.3 established by reading that
this is stale on a warm route — `NativeIncrementalCdcl::add_clause` moves the
core's count between solves and the adapter is never told — and predicted the
failure mode:

> The adapter's own `debug_assert_eq!(self.atom_for_var.len(), var, "variable
> indices are dense")` is what would fire — so the failure is **loud in debug
> and silent in release**.

**The diagnosis was right and that prediction is wrong**, which matters because
it is the half that would let somebody conclude a debug test run covers this.
The assertion compares `atom_for_var.len()` against the index the adapter is
about to push at. Both are the adapter's own bookkeeping, and a stale
`next_var` keeps them consistent **with each other** while both run behind the
core. Nothing in the adapter compares itself to the driver, which is the whole
defect.

Measured, with the fix reverted to the mirrored counter, on
`native_cdclt::tests::a_warm_adapter_maps_a_late_atom_onto_the_variable_the_core_appended_it_at`:

| profile | result | assertion raised |
|---|---|---|
| debug (default `cargo test`) | **`Unsat` on a satisfiable database** | none |
| `--release` | **`Unsat` on a satisfiable database** | none |

The mutant is behaviourally exact rather than approximate: the old `next_var`
equals `var_count + atoms-registered-so-far`, which is `atom_for_var.len()` at
all times while only atom pushes grow that vector, so shadowing the reported
parameter with `self.atom_for_var.len()` reproduces the deleted code.

### The fixture, and why it is a verdict

Two variables and two atoms are decided in a first solve. Then two clauses over
two **fresh** variables are added — the growth a mirroring adapter cannot see —
and the theory registers one atom.

- Correct: the core appends the atom at variable 4, which no clause constrains,
  the theory's "this atom may not hold" is satisfied by assigning it false, and
  the database is **satisfiable**.
- Mirrored: the adapter says variable 2, which the two added clauses jointly
  force TRUE. The theory rule is enforced against somebody else's clause
  variable and refutes a satisfiable database.

Two details are load-bearing and were chosen deliberately:

- The clauses are `[x3, x4]` and `[x3, -x4]`, which **entail** `x3` without
  either being a level-zero unit. With a unit clause the variable is assigned
  before registration extends the map, the theory is never told about it, and
  the misalignment is *deaf* rather than *wrong* — the run still returns `Sat`
  and the test passes over a corrupt map.
- The verdict is asserted **before** the map, so the failure message is the one
  that matters. Written the other way round the map assertion fires first and
  the wrong verdict never appears in the output.

Model validity is asserted, not model equality: the clauses and the theory rule
are both replayed against the returned assignment.

The fix: `NativeTheory::take_new_atoms` takes the driver's current variable
count. The theory cannot pull it — the driver holds the theory mutably borrowed
at that call — so the driver pushes it. `atom_for_var` is filled with `None`
below the reported index, because the variables in that gap are exactly the
non-atom ones `assert` must keep skipping.

---

## 2. B3 was not a swap, and the plan is wrong about a B4 blocker too

The plan scopes B3 as:

> it calls `backtrack_to_root` first thing, which is already the native
> between-solves discipline, so it is a swap once B2 exists.

`backtrack_to_root` is the easy half. Three things were missing, and one thing
the plan calls missing is not.

### 2.1 The session cannot hold the solver and the theory as siblings

`NativeTheoryAdapter<'a, T>` borrowed `&'a mut T`; `NativeIncrementalCdcl<T>`
**owns** its `T`; and `OnlineQuantifierClauseSession` holds both as sibling
fields and reaches past the driver to `EufTheory::add_atom_at_root`. That is a
self-referential struct.

Fixed by implementing `TheorySolver` for `&mut T` — mirroring
`axeyum_cnf::theory::NativeTheory for &mut T`, at the same place in the stack —
and making the adapter generic over its theory **by value**. The one-shot route
instantiates `NativeTheoryAdapter<&mut Theory>` and is unchanged; a warm route
instantiates `NativeTheoryAdapter<Theory>`.

### 2.2 Atom registration has to be driver-side, and it was not available

`CdclT::add_theory_variable()` returns `(variable, atom)` **synchronously**, so
the caller can put the variable into the clause it is building. The native
core's only registration channel is `NativeTheory::take_new_atoms`, polled by
`Cdcl::theory_round_body` at a propagation fixpoint *inside* a solve — after
the clause would have to already exist.

And for this theory the channel is not merely awkwardly timed, it is empty:
`EufTheory`'s `TheorySolver` impl is `assert`, `push`, `pop`, `propagate` and
nothing else (positive control: those four are what the impl block contains),
so `take_new_atoms` takes the trait default and returns `0` forever.

Added as `WarmNativeCdclT::add_theory_variable`: `reserve` appends the variable
non-branchable, `NativeTheoryAdapter::register_atom_variable` claims it for the
next atom.

### 2.3 The theory epoch closes lazily, and registration refuses to run inside one

`EufTheory::add_atom_at_root` returns `Err` unless its trail is empty, and the
warm object keeps the last solve's assertions so a model stays readable.
Without an explicit unwind, the first registration of every batch would be
refused and the session would silently disable itself. Added as
`NativeIncrementalCdcl::unwind_to_root`, the public counterpart of
`CdclT::backtrack_to_root`.

### 2.4 The plan's dormant-variable blocker is not real

> **B4** … it needs dormant variables, which do not exist in `axeyum-cnf` in
> any form.

They do. `NativeIncrementalCdcl::reserve` creates legal, **non-branchable**
variables (`Cdcl::branchable` exists and starts `false`), and
`Cdcl::add_input_clause` marks a literal's variable branchable when the clause
arrives. That is exactly `CdclT::add_theory_variable` (appends `active: false`)
plus `add_permanent_clause` (`activate_variables`). Whether B4's *mid-search*
insertion can use them is a separate question — `reserve` and `add_clause` both
require an unassigned solver — but the absolute claim is wrong and B4 should be
re-scoped against `reserve` before anyone prices it.

There **is** a real divergence in the same area, and the migration takes it
deliberately: `CdclT::new` marks every initial variable `active`, while the
native core marks only variables a literal mentions. A variable in no clause is
therefore decided by `CdclT` and not by the native core. `WarmNativeCdclT::value`
carries the same `occurring` filter `NativeModel` applies on the one-shot path,
which reports `None` for those — the answer `CdclT::value` gives for a variable
it never decided. This is the choice the already-migrated one-shot routes made.

---

## 3. Verdict invariance, measured on three axes

**Population:** `bench-results/parity-losses-20260908/UF.txt` (32 files) and
`bench-results/parity-losses-20260906/UF.axeyum-only24.txt` (24 files). 56
files, every one compared **per file**, never only in aggregate.

**Protocol:** the SCORED recipe from
`bench-results/parity-losses-20260908/README.md` —
`MEM_LIMIT_GB=8 timeout 29 env -u AXEYUM_EVIDENCE scripts/mem-run.sh
target/release/examples/smtcomp_cli <file> --timeout-ms 24000` — on eight
`taskset`-pinned core pairs. Baseline arm built from commit `5c2e6a818` in a
`scripts/lane-snapshot.sh` tree with its own target directory, so the two
binaries never share a build cache. Host load 4.67 at the baseline launch and
5.18 at the migrated launch.

### 3.1 Verdicts

| list | files | baseline decided | migrated decided | files whose verdict moved |
|---|---:|---:|---:|---:|
| `UF.txt` (losses) | 32 | **4** (all `unsat`) | **4** (all `unsat`) | **0** |
| `UF.axeyum-only24.txt` (wins) | 24 | **24** (22 `sat`, 2 `unsat`) | **24** (22 `sat`, 2 `unsat`) | **0** |

Both bars held. The brief cited 3 of 32 for the loss list; this measurement
reads **4** on *both* arms, so the number is a day-and-load difference in the
baseline, not a change from the migration. The remaining 28 loss files are 26
`unknown` and 2 that printed no verdict inside the external 29 s kill; those two
are the same two files on both arms.

### 3.2 Give-up reason strings

A separate `--trace` pass, both arms, all 56 files, comparing the
`; give-up kind=… detail=…` line per file.

| verdict + reason | baseline | migrated |
|---|---:|---:|
| `unsat` | 4 | 4 |
| `unknown`, `kind=Incomplete detail=e-matching instantiation did not refute within the round budget` | 18 | 20 |
| `unknown`, no reason line captured | 8 | 6 |
| no verdict line captured | 2 | 2 |
| `sat` (win list) | 22 | 22 |
| `unsat` (win list) | 2 | 2 |

**Two files appear to move, and they do not.** Both move from *no reason
captured* to *the reason above* — a reason appearing, never one reason becoming
a different one. A missing line under an external wall clock is ambiguous
between "the solver reported nothing" and "the process was killed before it
printed", so each was re-run three times on **each** arm with the external
timeout raised to 120 s:

| file | baseline reps with the reason | migrated reps with the reason |
|---|---:|---:|
| `…/nada/distro/gram_lang/x2015_09_10_16_53_37_371_1432776.smt_in.smt2` | 3 of 3 | 3 of 3 |
| `…/sledgehammer/Fundamental_Theorem_Algebra/uf.1158058.smt2` | 2 of 3 | 2 of 3 |

The first is a sweep artifact outright. The second flips on **both** arms at the
same rate, so it is run-to-run noise on a wall clock and the baseline exhibits
it too. The verdict on both files is `unknown` in every one of the twelve runs.
**Give-up reason: invariant.**

### 3.3 Models — validity, not equality

`qinst_egraph` feeds instantiation from the model its online session is handed
(`true_equality_terms` → `scoped_candidate_instances`), which is the
MBQI-shaped consumer the hazard note in `native_cdclt.rs` is about. So models
were checked, and **validity** is what is claimed:

All 28 decided files through `smtcomp_cli --evidence` on both arms, reading the
arena-backed re-validation — `Evidence::check_outcome` against a **fresh parse**
of the original file, which for a `sat` replays the model against the original
terms and can return `FAIL`:

| | baseline | migrated |
|---|---|---|
| `sat`, `kind=sat-model certified=1 recheck=na arena=ok` | 22 | 22 |
| `unsat`, `kind=unsat-uncertified … arena=none:uncertified-unsat` | 5 | 5 |
| `unknown` under the evidence configuration | 1 | 1 |
| files whose evidence line moved | — | **0** |

Every `sat` model replayed, on both arms, and the per-file diff is empty.
(The one `unsat`→`unknown` shift against §3.1 is the evidence configuration,
not the migration: it is the same file on both arms. Evidence is ON here and
OFF in the scored protocol, deliberately, so these two tables are not mixed.)

**Model equality is not claimed and was not checked.** E3 measured that a warm
model is not a one-shot model and cannot be, phase retention being what warmth
is. What §3.1–3.3 establish is that wherever the session's internal model
differs, the loop's *outcome* does not — which is the thing that matters and is
not implied by SAT-layer equivalence.

### 3.4 The session is live, not silently disabled

A migration that quietly declines is verdict-invariant for the wrong reason.
`qinst_egraph::tests::recursive_provenance_chain_reduces_complete_instance_volume`
is the guard that rules it out, and it passed unchanged: it asserts
`online_solves > 0`, `online_clauses > 0`, and
`online_qf_checks < fresh_qf_checks` — "retained clauses must eliminate at least
one complete QF rebuild". The native session inserts clauses, solves, and still
saves the rebuilds the `CdclT` session saved.

### 3.5 What this does not establish

- **No timing claim.** The sweep script's `date +%s%3N` produced a malformed
  millisecond field, so every wall-clock number it recorded is junk and none is
  quoted here. Verdicts and reason strings come from the process output and are
  unaffected. Nothing in this note is a performance measurement, which is
  correct for B3 — verdict invariance is the deliverable.
- **Two files never print a verdict** inside the external kill, on both arms.
  They are counted as undecided and their reasons are not compared.
- The `axeyum-bench` corpus harness was tried first for model replay and
  reported `unsupported=28`, so its `model_replay_failures=0` was a **vacuous
  zero** on this population. It is recorded here because that zero is exactly
  the shape of a checker that cannot fail; §3.3 uses a route whose `FAIL` is
  reachable instead.

---

## 4. Gates, with exit codes read directly and never through a pipe

| gate | result | exit |
|---|---|---:|
| `test -p axeyum-solver --lib --features full -- --test-threads=4` | **1696 passed**, 0 failed (1695 before, +1 the new guard) | 0 |
| `test -p axeyum-cnf --lib` | **634 passed**, 0 failed | 0 |
| `test -p axeyum-solver --features full --test corpus_regression` | 2 passed, 0 failed | 0 |
| `test -p axeyum-solver --features full --test quant_skolem_egraph_routing` | 1 passed, 0 failed | 0 |
| `clippy --workspace --all-targets -- -D warnings` | clean | 0 |
| `cargo fmt --all --check` (read-only) | clean | 0 |

Everything heavy through `scripts/cargo-serialized.sh`.

Not run, and therefore not claimed: `just check`, `./scripts/check.sh`, the
`--features z3` differential fuzzes (this change touches neither linear
arithmetic nor the string routes), and `progress_frontier`.

## 5. What B5 inherits

`CdclT` now has **no CDCL(T) client in `src/`**. `backtrack_to_root` and
`value` are dead outside its own tests and are retained under
`#[cfg_attr(not(test), expect(dead_code, reason = "ADR-1908 B5: CdclT is
retained as the oracle"))]`: ADR-1908 demotes `CdclT` to the differential
oracle for the native core, and an oracle missing the incremental half of its
protocol cannot adjudicate the route that used it. Deleting them is B5's call,
and B5 now also owns the thing this lane did not build — a **running**
differential between `WarmNativeCdclT` and the `CdclT` session it replaced. The
56-file population above is a verdict comparison across a commit boundary, not
a gate that runs.
