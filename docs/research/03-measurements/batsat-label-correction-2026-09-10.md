# Correcting the BatSat labels — what changed, and the bench-artifact decision

Date: 2026-09-10
Lane: `E1-batsat-labels`
Subject: phases **A2** and **A3** of
[12-cdcl-consolidation-plan.md](../../solver-comparison-2026-09/12-cdcl-consolidation-plan.md),
executing the W-class and section-2e findings of
[batsat-slice2-surface-2026-09-10.md](batsat-slice2-surface-2026-09-10.md).

This lane changed **labels and prose only**. The `batsat-reference` feature,
the three optional dependencies, the differential suite and every gated test
are untouched — that is phase A4 and it is blocked on a replacement referee.
No behaviour changed anywhere.

Commits: `2923ed8a0` (A3, code), `e5a7b0082` (A2, twelve docs + three checker
pins), `e06ed8b8d` (A2, the thirteenth doc + regenerated `PLAN.md`).

## 1. The judgement call — the mislabelled bench artifacts

`crates/axeyum-bench/examples/cnf_stream_bench.rs` emitted a JSON key literally
named `"batsat"` for numbers `IncrementalSat` produced, and ADR-1703 re-based
`IncrementalSat` on the in-tree native CDCL core. Renaming a key changes the
schema a consumer reads, so the question had to be answered before the edit:
**who reads it, and what happens to what has already been written?**

### Who reads it: nobody

| Question | Command | Result |
|---|---|---|
| does anything parse the key? | `git grep '"batsat"' -- '*.py' '*.sh' '*.rs' '*.js'` | 7 hits, **all writers or unrelated prose; zero readers** |
| does anything name the schema? | `git grep 'axeyum-persistent-cnf-stream-benchmark'` | 2 hits: the example itself, and one artifact |

The other two writers of a `batsat` JSON key — `cnf_core_bench.rs:195` and
`gate_b_sweep.rs:219` — are both gated on `batsat-reference`, so their key is
**correct** and was left alone. Only `cnf_stream_bench` writes it on a default
build.

### What has already been written: one artifact, and it is correctly labelled

Exactly one artifact with this schema is tracked:

```
bench-results/glaurung-dptf-persistent-cnf-20260717/report.json
  schema : axeyum-persistent-cnf-stream-benchmark-v1
  rows   : 2155
  written: 2026-07-17  (git log -1, commit 6ea7cde87)
```

2026-07-17 is **seven weeks before ADR-1703** (2026-09-05). Its `batsat` rows
really were produced by BatSat. It is accurate.

So the survey's line — *"every artifact this example has written since
2026-09-05 labels native-core numbers `batsat`"* — is right about the **code**
and describes a **prospective** hazard. The set of mislabelled artifacts in
tree is **empty**: no run of this example was ever committed after ADR-1703.
That is the fact that made the decision easy, and it is worth stating plainly
because the plan and the survey both read as though a corrupted artifact
corpus existed.

### Decision

1. Rename the per-row key `"batsat"` → `"native_core"`.
2. Bump the report schema `axeyum-persistent-cnf-stream-benchmark-**v1**` →
   `**v2**`.
3. **Leave `bench-results/glaurung-dptf-persistent-cnf-20260717/report.json`
   exactly as it is.** It is a recorded measurement, it is correctly labelled
   for its engine, and `bench-results/` is never edited (survey §8 Tier E).
4. State the v1/v2 rule in the example's own module doc, so a reader of either
   version knows which engine produced the numbers:

   > a `v1` report's `batsat` row really was produced by the `BatSat` adapter,
   > a `v2` report's `native_core` row is the native core.

The schema bump is the load-bearing half. Renaming the key alone would have
made the old and new artifacts indistinguishable to a consumer that keyed on
the schema string; with the bump, the version *is* the engine attribution and
no consumer has to know the ADR-1703 date. This follows the precedent already
in tree: `scripts/summarize-glaurung-repetitions.py:257` accepts **both** the
old and new `primary_search` unit strings for exactly this reason, with an
ADR-1703 comment saying pre-commit artifacts keep the old unit and are still
accurate.

No re-labelling or re-generation of existing artifacts was needed, and none was
done.

## 2. A3 — the six live `.rs` files

All six already called the native core; only names, strings and comments said
batsat.

| File | What changed |
|---|---|
| `axeyum-bench/examples/cnf_stream_bench.rs` | module doc; `BatState` → `NativeCoreState`; `bat_*` locals → `core_*`; mismatch message `BatSat=` → `native_core=`; the JSON key and schema (§1) |
| `axeyum-cnf/src/xor_cdcl.rs` | `learning_required_matches_batsat_on_chain` → `..._matches_native_core_on_chain`; `differential_vs_batsat_random` → `differential_vs_native_core_random`; 3 `expect`s, 1 assert message, 1 comment |
| `axeyum-cnf/src/xor_dpll.rs` | `differential_vs_batsat_random` → `differential_vs_native_core_random`; 1 `expect`, 1 panic message |
| `axeyum-search/examples/akb2_frontier.rs` | module doc, 1 comment, 1 `expect` |
| `axeyum-solver/tests/xor_cdcl_fallback.rs` | 5 comments, 2 assert messages |
| `axeyum-py/src/solver/core.rs` | the `unsendable` justification (see below) |

Both renamed test functions were checked for external references first
(`git grep`): only the dated survey note names them, so nothing depended on the
old names. **They remain real differentials** — CDCL(XOR) and naive XOR-DPLL
against the native core, 500 and 300 random formulas on a default build. Only
the referee's name was wrong, and their value is unchanged.

### `unsendable` was NOT relaxed

`crates/axeyum-py/src/solver/core.rs:647` justified `#[pyclass(unsendable)]`
with *"the warm solver embeds a BatSat solver whose callback structs hold
`Cell`s, so it is `Send` but `!Sync`"*. The premise is provably false —
`IncrementalSat`'s field is `NativeIncrementalCdcl` — but the **conclusion** is
a separate question that this lane **did not measure**: no `Send`/`Sync`
assertion was run. The attribute is therefore **retained**, and the comment now
says so explicitly rather than trading one confident claim for another.
Determining it is survey §8 Tier B item 10.

## 3. A2 — the thirteen docs

All thirteen were re-read at the named line before editing. All thirteen were
wrong. None was a broken command (the survey established that separately with a
positive control, and this lane ran nothing to re-verify a claim).

**Nine are one sentence copied nine times**, and deleting the word "BatSat"
would have left the wrong half standing. The claim was *"BatSat is what solves,
so UNSAT is proofless"* — the assurance half is what ADR-1703 overturns:

> With the native core on every path, that boundary **disappears rather than
> moves** … "Proofless UNSAT" stops being a category of result Axeyum can
> produce and becomes a per-call choice not to spend the proof-checking time.

The default route is still stamped `Unchecked` — emission is off by default for
speed — so every rewrite **keeps the `Unchecked` status and replaces the
reason**, and carries ADR-1703's own two caveats (warm-path emission off by
default; an `unsat` under assumptions carries a failed-assumption core, not a
refutation).

### Three checker pins, not one

The plan and the survey both name `scripts/check-parity-docs.py:1295` as *the*
trip-wire. Grepping the checker for `batsat` returns **three** marker strings,
and every one of them pins a sentence in this lane's list:

| checker line | marker | doc |
|---|---|---|
| `:890` | `default BatSat-backed clausal route reports raw UNSAT` | W6 `learn/05` |
| `:935` | `default proofless BatSat result remains lower assurance` | W7 `proof-cookbook` |
| `:1295` | ``default BatSat adapter remains lower-assurance `Unchecked` `` | W9 `research-questions` |

All three moved in the same commit as their doc. A **fourth** pin,
``(LEARN_PIPELINE, "proof status as `Unchecked`")``, sits on the W5 sentence;
its substring is deliberately preserved by the rewrite, so it needed no change.

**The four guards are live, not decorative.** Mutation-tested one at a time —
corrupt the pinned sentence, run the checker, restore. Each produced **exit 1
and exactly one new error, naming that marker**. The tree was verified restored
to its 101-error baseline afterwards.

### Two claims that were wrong in a way the survey did not state

Both were settled by reading the code, not the prose. W8 and W10 each assert
that the bench *"records the actual Cargo.lock-pinned BatSat defaults (seed
`91648253`, …)"* and that the resource unit is *"`BatSat` `within_budget`
progress checks on the default path"*. Measured:

| claim | check | result |
|---|---|---|
| the seed is recorded | `git grep 91648253 -- crates/` | **0 hits** (positive control: 3 `docs/` files still carry it) |
| what the profile records | `determinism_record()`, `axeyum-bench/src/main.rs:6767` | `NATIVE_CDCL_ENGINE_ID` and `"randomness": "none"`, with a comment saying a seed would be decoration |
| the resource unit | `resource_profile_record()` | `primary_search_unit = "native proof-CDCL conflicts"`, unconditional, ADR-1703 comment |

Both rewrites name the old seed and unit as what **pre-ADR-1703 artifacts
carry**, so the docs now agree with
`scripts/summarize-glaurung-repetitions.py`, which validates both.

### One site the survey missed

Correcting W8 and W10 would have left the docs disagreeing with their own
authority:

> `crates/axeyum-solver/src/backend.rs:104` — the doc for
> `SolverConfig::resource_limit` still said the unit is `` `BatSat`
> `within_budget` progress checks on the cold SAT-BV path ``.

That is the exact field W8 and W10 describe, and it contradicts
`crates/axeyum-cnf/src/lib.rs:808`, which already says the unit is the native
core's conflict count. The survey's §2f lists four wrong doc comments and this
is not one of them (`backend.rs:560` is a different site). Corrected here.

### What was deliberately left true

A fourth reading was cheap and it changed three decisions:

- **Source-Pointers URL lists** and the settled ``[x] Which pure Rust SAT
  solver is the first adapter? — Answer: `rustsat-batsat` `` items. The answer
  **to the question as asked** is still true and records a real decision. Each
  now carries a one-line note that ADR-1703 superseded it as the *engine*;
  none was rewritten or deleted.
- `benchmarking-and-performance-methodology.md:686` — *"on Dptf … retained
  BatSat beats retained Z3 Boolean by a 3.5527x per-call solve geomean"*. That
  is the 2026-07-17 measurement, from the very artifact discussed in §1. It
  really was BatSat. **Historical and true; untouched.**
- `:664` — *"BatSat fresh import/solve"* describes what `cnf_core_bench` must
  distinguish, and that example is still gated on `batsat-reference`. Still
  correct for that command.

### W13 is a queue entry and got its own commit

`docs/plan/global/20-next-actions.md` recommendation 2 proposes running the
four-engine gate-(b) sweep and says *"no CaDiCaL or Kissat run exists under
`bench-results/` today"*. It ran on 2026-09-05; the artifact is
`bench-results/sat-core-gate-b-20260905/` and the decision is ADR-1703. A lane
picking this up would spend a day re-measuring a settled question.

Marked DONE with its result inline rather than deleted. The entry bundled **two**
questions and gate (b) answered only one: whether `CdclT` should be replaced
rather than tuned is **still open** — ADR-1703 does not mention `CdclT` at all.
So its **Stop** clause was not removed, only re-pointed: the block on the
theory-trait widening is lifted as far as the Boolean engine goes, and now
names Phase B0 (write the `CdclT` ADR) as what still gates it.

`PLAN.md` was **regenerated**, not edited — this file is embedded in it, so the
two diffs are the same 45 lines. `MERGE_HEAD` was checked absent first. Kept as
a separate commit because `docs/plan/global/` is the shared queue and `PLAN.md`
is the highest-contention file in the repository; dropping this one commit
costs nothing and leaves the other twelve intact.

## 4. Gates

Exit codes read directly, never through a pipe.

| gate | before | after |
|---|---|---|
| `python3 scripts/check-parity-docs.py` | **1** (101 ERROR) | **1** (101 ERROR) |
| `./scripts/check-links.sh` | — | **0** (`all links ok`) |
| `scripts/check-merge-hygiene.sh` | — | **0** (PASS, `generated=current`) |
| `python3 scripts/gen-plan.py --check` | — | **0** |
| `rustfmt --edition 2024`, per file (7 files) | — | **0** |
| `clippy -p axeyum-cnf --all-targets -D warnings` | — | **0** |
| `clippy -p axeyum-search --all-targets -D warnings` | — | **0** |
| `clippy -p axeyum-solver --all-targets --features full -D warnings` | — | **0** |
| `clippy -p axeyum-py --all-targets -D warnings` | — | **0** |
| `clippy -p axeyum-bench --all-targets --features z3 -D warnings` | — | **101**, see below |

**`check-parity-docs.py` was already red on `main`** before this lane started,
for reasons unrelated to batsat (the `docs/reference/examples.md` Cargo-example
inventory, the 253-example markers in `docs/documentation-plan.md` and
`PLAN.md`, and four `docs/PROJECT-STATE.md` parity rows). A matching exit code
is not evidence, so the two ERROR sets were sorted and diffed: **byte-identical
— zero new failures, zero incidentally fixed.** That pre-existing failure needs
an owner and is not this lane's.

**`--features full` and `--features z3` are load-bearing on those clippy
lines.** `xor_cdcl_fallback.rs` is `#![cfg(feature = "full")]` and
`cnf_stream_bench` carries `required-features = ["z3"]`, so without them clippy
compiles neither file and exits 0 over code it never read.

**The `axeyum-bench` 101 is not from this lane.** It is
`crates/axeyum-bench/examples/qfuf_rung_timing.rs`, three `clippy::doc_markdown`
errors, **byte-identical to `main`** (`git diff main --name-only` on that path
is empty), landed today in `4d2fdf068`. No error in that run names any file
this lane touched. Reported rather than fixed: **`main` is red on that gate**
and its owner should know. This lane's own two `doc_markdown` errors in
`cnf_stream_bench.rs` were found by the same run and fixed before commit.

## 5. What this lane did NOT do

Reported as "did not run", never inferred.

- **The four wrong doc comments of survey §2f** (Tier B item 6):
  `axeyum-cnf/src/lib.rs:5`, `axeyum-solver/src/sat_bv_backend.rs:4`,
  `axeyum-solver/tests/sat_bv.rs:4`, `axeyum-solver/src/backend.rs:570`. They
  are a separate item from A2 and A3 and are still wrong. Note for whoever
  takes them: `scripts/tests/test-admission-limit-basis-control.sh:70-78`
  reasons about `lib.rs` "still saying batsat in prose" — read that comment
  before editing `lib.rs:5`. (The control's own logic survives, because the
  gated `#[cfg(feature = "batsat-reference")]` re-export keeps the word.)
- **Whether `IncrementalBvSolver` is still `!Sync`.** No `Send`/`Sync`
  assertion was run. `unsendable` retained.
- **`SolverConfig::native_cdcl`** (survey §2i, Tier B item 9). Not touched;
  A0 (`da911539a`) corrected its doc and this lane changed nothing further.
- **Any full-workspace build, `cargo test`, `check.sh` or `just check`.** The
  five per-crate clippy runs above are what was run. No test suite was executed
  by this lane, and no claim here rests on one.
- **A4** — the feature and dependency removal. Untouched by design.

## 6. Residual surface, measured after the change

| population | before | after |
|---|---:|---:|
| `docs/` files mentioning batsat/rustsat | **115** at `8ddb066e4` | **114** |
| of which live-and-wrong (W) | **13** | **0** |
| live `.rs` files that say batsat while calling the native core (§2e) | **6** | **0** |
| wrong `.rs` doc comments (§2f, out of scope) | 4 | 4 |

**Quote the tree with the number.** The survey measured **110** at
`f91570117`; the same sweep on this lane's base `8ddb066e4` returns **115**,
because five more `docs/` files gained a batsat mention in between (the R-B
survey note itself among them, exactly as it predicted). Both numbers are right
about their own tree. This lane's own note will make it 115 again once
committed.

The count went **down** by one, and the file that left is worth naming:
`docs/user-guide/benchmarks.md` (W8) no longer mentions batsat **at all** —
correcting its three claims removed every occurrence. Every other edit kept the
word, because in each the honest correction is to say what BatSat *used to* do.

Verification that the W row is really 0, rather than a grep that missed: each
of the ten distinct wrong phrases was grepped back over `docs/` and `crates/`
after the edits. The only survivors are two lines in
`docs/research/09-decisions/adr-0136-qfbv-client-integration-and-benchmark-boundary.md`,
which is an **ADR** — class H, Tier E item 19, keep forever. It records what was
decided when it was decided and is correctly untouched.

Positive control on the same grep: `axeyum-cnf` matches 238 `docs/` files, and
`BatSat` matches ADR-1703 22 times, so the empty results above are real
negatives and not a broken pattern.
