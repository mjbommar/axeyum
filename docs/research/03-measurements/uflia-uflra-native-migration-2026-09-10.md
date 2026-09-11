# `uflia_online` + `uflra_online` onto the native core: the before/after columns

Phase B1 of
[the CDCL(T) consolidation plan](../../solver-comparison-2026-09/12-cdcl-consolidation-plan.md),
under [ADR-1908](../09-decisions/adr-1908-the-native-core-is-the-one-cdclt-driver-cdclt-is-demoted-to-an-oracle.md).
Lane `E2-uf-arith-migrate`, 2026-09-10, host `s4`.

**Result: verdict-, reason- and model-invariant on every population measured.**
Zero verdict changes, zero give-up-reason changes, zero model-byte changes. The
one thing that moved is wall clock, and it moved *down* on the files that
decide.

---

## 0. What the inventory got right, and the one thing it did not

R-A's [migration inventory](cdclt-native-migration-inventory-2026-09-10.md)
called C3/C4 "nothing structural, two small things and one risk", and named the
blocker as *"`theory_propagations` is not returned by `solve_native`"*. That is
right as far as it goes. **The counter is not merely unreturned — it is not
counted at all on a default run**, and that is the difference between "a few
lines on `NativeSolveOutcome`" and a decision about what the native core
measures:

```rust
// proof_sat.rs, before this change
self.enqueue(lit, reason);
if self.collect_layer_stats {
    self.stat_theory_propagations += 1;
}
```

`CdclT` counts it unconditionally (`cdclt.rs:1442`). The two routes hand the
number back through the public `check_qf_uf{lra,lia}_boolean_prop_metrics`, and
their callers run on a **default** config with no `--trace` collection. So a
naive swap makes a live number report a measured zero — the `cb5cd9090` shape,
where *an absent number reads as a settled one*.

**This is not an inference. It was measured, by mutation.** With the increment
left gated and the routes migrated:

```
crates/axeyum-solver/tests/uflra_online.rs:934:
  combined theory propagation never fired through CdclT (0)
```

So the fix is to **ungate that one counter** (a `u64` increment, not a clock
read — every other guard in `proof_sat.rs` exists to skip an `Instant::now()`,
and this one has nothing to skip), and to document the exception at all four
places that state the "all-zero unless collection is on" contract.

### The guard on the exception

`proof_sat::layer_stats_tests::an_untraced_solve_reports_the_all_zero_snapshot`
became
`an_untraced_solve_is_all_zero_except_the_route_visible_propagation_count`, and
is discriminating **in both directions**:

- it asserts `theory_propagations > 0` on an untraced run, so re-gating the
  increment fails it;
- it compares every *other* field against `Default` through
  `NativeLayerStats { theory_propagations: 0, ..stats }`, so ungating any other
  counter or `Duration` fails it too — and a field added to the struct later is
  covered without the test being edited.

**Mutation control, run:** re-gate the increment → `-p axeyum-cnf --lib` goes
`618 passed` → `617 passed; 1 failed`, and the one failure is exactly that test.
Exactly one guard dies.

---

## 1. What changed

| file | change |
|---|---|
| `crates/axeyum-cnf/src/proof_sat.rs` | `stat_theory_propagations` ungated; the contract documented at its four statement sites; the all-zero test rewritten as above |
| `crates/axeyum-solver/src/native_cdclt.rs` | `solve_native_counted` returns `(NativeSolveOutcome, usize)`; `solve_native` delegates to it. The count is returned on **every** outcome, `Unknown` included, because `CdclT`'s callers read it before matching on the verdict. Module route table corrected: it named `ufbv_online` as the sole incremental client and omitted `qinst_egraph`, which was a second one in the same commit |
| `crates/axeyum-solver/src/uflia_online.rs` | `cdclt_combined` C3: `CdclT::new(..).solve(..)` → `solve_native_counted`; `solver.value(v)` → `NativeModel::value` |
| `crates/axeyum-solver/src/uflra_online.rs` | `cdclt_combined` C4: same |
| `crates/axeyum-solver/src/cdclt.rs` | `CdclT::theory_propagations` is now `#[cfg(test)]` — its last shipping consumers were the two routes above; every remaining caller is a unit test of the driver in its ADR-1908 role as differential oracle |

No conversion layer was needed: `solve_native` already takes `crate::cdclt::Lit`
clauses, and `theory_atom_count` has the same meaning as `CdclT::new`'s second
argument.

---

## 2. Coverage — check this before reading §3

**The parity slice does not exercise the migrated code on every file, and
saying which files it does is the difference between a measurement and a
coincidence.** Measured with a temporary `eprintln!` at the top of both
`cdclt_combined` bodies, one process per file, on the pre-migration tree:

| `bench-results/parity-losses-20260908/QF_UFLIA.txt` | files | reach `cdclt_combined` |
|---|---:|---:|
| **whole slice** | 23 | **12** |
| — of which `sat` | 5 | **5** |
| — of which `unsat` | 5 | 0 |
| — of which `unknown` | 13 | 7 |

So 11 of the 23 decline before the migrated function (atom caps, out-of-fragment
atoms, an unsupported skeleton op) and are, for this change, controls rather
than subjects. The five `unsat` verdicts on the slice come from somewhere else
entirely.

What makes the slice worth running anyway: **all five `sat` verdicts go through
the migrated route.** That is the risky class — both sites are model-based
consumers behind a replay gate, so a different-but-correct model is a
`Sat` → `Unknown` regression (the `f429b3b8a` shape), and the slice hits it
head-on.

Because 12 of 23 is thin, three further populations were measured (§3.2, §3.3).

---

## 3. The columns

### 3.1 The QF_UFLIA parity slice, through the front door

`target/release/axeyum <file> --timeout-ms 20000`, prebuilt release binaries
(not the cargo wrapper — that takes a host-wide flock and would time the queue),
one process per file, both trees.

| verdict | before | after |
|---|---:|---:|
| `sat` | 5 | **5** |
| `unsat` | 5 | **5** |
| `unknown` | 13 | **13** |

`diff` of the per-file verdict columns: **empty. All 23 identical.**

The front door does not answer `(get-info :reason-unknown)`, so give-up reasons
are compared at the route instead — §3.2.

### 3.2 The same 23 files, route in isolation, verdict **and** reason

`route_solo --route uflia-online --timeout-ms 10000`. This is deliberately *not*
the front door (it decides the flat assertion view and applies no preprocessing,
so its verdicts are a lower bound), but it is the only channel that prints the
full `UnknownReason`, which is the thing `ea85c9813` moved without moving a
verdict.

Comparing columns `file`, `route`, `verdict`, `detail` — everything but
`wall_ms`:

```
diff <(cut -f1,2,3,5 solo-uflia-before.tsv) <(cut -f1,2,3,5 solo-uflia-after.tsv)
→ empty, exit 0
```

**23 of 23 identical, reason string included**, across five distinct decline
details (`too many theory atoms for opaque-app online UFLIA`, `atom outside
QF_UFLIA while building the online UFLIA combined state`, `too many theory atoms
for the online combination boolean layer`, `boolean skeleton outside the online
combination encoder`, `combined CDCL(T) leaf did not rebuild a replaying model:
interface distinct branch inconclusive`).

### 3.3 Two wider populations, because 12 of 23 is thin coverage

There is **no preregistered QF_UFLRA loss list** — `parity-losses-20260908/`
has none — so this lane constructed samples and labels them as such. Both are
deterministic (`find | sort`), not random, and neither is a blind evaluation
population.

| population | construction | files | decided | reach the route |
|---|---|---:|---:|---|
| QF_UFLRA, spread | every 26th of 1,284 sorted paths | 50 | 4 | poor — **26 of 28 unknowns decline at the 8,192-atom cap before `cdclt_combined`** |
| QF_UFLRA, small | the 80 smallest by byte size | 80 | **36** (14 sat, 22 unsat) | good — 18 more unknowns come from *inside* the driver |
| QF_UFLIA, small | the 80 smallest by byte size | 80 | **33** (13 sat, 20 unsat) | good — 42 more unknowns come from inside the driver, ~75 of 80 exercise it |

The first sample is reported rather than dropped: **it is the one that shows the
cap, not the engine, is what most QF_UFLRA files hit**, which is a fact about
where this route's remaining gap lives and is not something the migration
changes.

`diff` on `file`, `route`, `verdict`, `detail` for all three:

| population | verdict + reason diff |
|---|---|
| QF_UFLRA spread (50) | **empty** |
| QF_UFLRA small (80) | **empty** |
| QF_UFLIA small (80) | **empty** |

### 3.4 Models, byte for byte

A replay gate turns a *non*-replaying model into `Unknown`, so §3.1–3.3 already
rule out a model that stopped replaying. They do **not** rule out a
different-but-still-replaying model, which is exactly what cost a verdict in
`f429b3b8a` — MBQI picks instantiation terms out of the model it is handed.

So: `(get-model)` appended to each satisfiable file, full stdout SHA-256, both
binaries.

| set | files | models identical |
|---|---:|---|
| the 5 `hash_sat_*` files of the parity slice (all five go through the route) | 5 | **5 / 5** |
| every file the small samples decided `sat` | 27 | **27 / 27** |

**32 satisfiable queries, 32 byte-identical models.** That the models did not
move at all is what `solve_native`'s pinned `initial_phase: true,
target_rephase: false` is *for*; this is that pin measured on these two routes
rather than inherited from the commit that introduced it.

### 3.5 Wall clock — advisory only

Single run, shared host, no reference-frame calibration. **Do not raise a
baseline from this.** Reported because it is the only column that moved:

| file (`uflia-online`, solo, ms) | before | after |
|---|---:|---:|
| `medium9.smt2` | 33 | 20 |
| `medium10.smt2` | 36 | 22 |
| `medium13.smt2` | 92 | 44 |
| `medium16.smt2` | 178 | 75 |
| `medium19.smt2` | 262 | 166 |

Five `unsat` files, all faster, 1.6–2.4×. **This is not a claim that the native
core is faster than `CdclT`** — five files on one loaded box is not that claim,
and ADR-1908 records "unknown, and not claimed" deliberately. It is recorded so
the next lane knows which direction to look.

---

## 4. Gates

Every count stated, because three of these compile to zero tests and exit 0
without their feature flag.

| gate | result |
|---|---|
| `-p axeyum-cnf --lib` | **618 passed**, 0 failed |
| `-p axeyum-solver --lib --features full -- --test-threads=4` | **1,695 passed**, 0 failed (301 s) |
| `-p axeyum-solver --features full --test corpus_regression` | **2 passed**, 0 failed |
| `-p axeyum-solver --features full --test uflra_online` | **21 passed**, 0 failed |
| `-p axeyum-solver --features full --test uflia_online` | 32 passed, **1 failed — pre-existing, see §5** |
| `-p axeyum-solver --features z3 --test qf_uflra_differential_fuzz` | **1 passed**, 0 failed |
| `-p axeyum-solver --features z3 --test qf_lia_differential_fuzz` | **4 passed**, 0 failed |
| `-p axeyum-solver --features z3 --test uflia_differential_fuzz` | **2 passed**, 0 failed |
| `-p axeyum-solver --features z3 --test uf_arith_dispatch_differential` | **2 passed**, 0 failed |
| `-p axeyum-solver --features z3 --test qf_uf_differential_fuzz` | **1 passed**, 0 failed (301 s) |
| `cargo fmt --all --check` | clean (exit 0, read directly) |
| `check --workspace --all-targets` | clean |

The last three z3 suites are not in the brief's list and were added because they
are the ones that actually cover this arm: `uf_arith_dispatch_differential` is
named in `auto.rs` as *"the load-bearing gate on this invariant"* for the
online-first UF+arithmetic dispatch, and `uflia_differential_fuzz` is the only
z3 oracle over the UF+LIA combination itself (`qf_lia_differential_fuzz` has no
UF in it).

**Not run, and not claimed:** `progress_frontier`, `./scripts/check.sh`,
`just check`, `cargo deny`.

---

## 5. A pre-existing failure this lane did **not** cause

`uflia_online::opaque_app_interface_overflow_declines_without_enumerative_fallback`
fails, and it fails **identically on the merge base**. Verified by reverting all
five changed files to `HEAD` and re-running: the same test, the same byte-for-byte
panic message.

```
opaque-app layouts that exceed the incremental interface split should not
restart the unsafe enumerative fallback, got Unknown(UnknownReason {
  kind: Incomplete,
  detail: "combined CDCL(T) leaf did not rebuild a replaying model:
           combined model build failed (LIA model unavailable: overflow,
           coverage, deadline, or an integer-search cap)" })
```

The test expects a decline naming *"opaque-app online UFLIA incremental combined
state could not be built safely"*, which is raised at
`CombinedIncrementalLia::new_explained` — **before** `cdclt_combined` runs, and
therefore upstream of everything this lane touched. It carries a 100 ms budget,
which is the likely reason it drifted. It is left alone: fixing it is a
different diagnosis, and pinning it here would have hidden that the failure
predates the migration.

---

## 6. Method, and what did not run

- **Both binaries are prebuilt `--release`**, never the cargo wrapper, because
  `cargo-serialized.sh` takes a host-wide flock and a timing run through it
  measures the queue.
- **The "before" tree is the real thing, not a reconstruction.** All five
  changed files were copied aside and `git checkout --`'d, the binaries rebuilt
  from that tree, and the files restored afterwards. Both `route_solo` binaries
  were built this way, so the comparison is between two compiled trees.
- **The coverage probe (§2) was a temporary `eprintln!`** in both
  `cdclt_combined` bodies, built, measured, and reverted. It is not in the diff.
- **Did not run:** any measurement of whether the native core is faster on
  these routes beyond the five advisory rows in §3.5; any QF_UFLRA front-door
  parity comparison (there is no preregistered list to compare against); the
  aggregate gate; `progress_frontier`.
- **The QF_UFLRA samples are this lane's construction**, not a preregistered
  population, and are labelled so wherever they are quoted. They must not be
  cited as "the QF_UFLRA loss set".
