# Phase 0 integration result — 2026-07-28

Result note for [`agent-program-2026-07-28/phase-0-integration.md`](agent-program-2026-07-28/phase-0-integration.md).
Base `ffc466b4` → `main` after this session.

**Headline: a P0 wrong-`unsat` was found and fixed during integration.** It was
reachable from a four-line SMT-LIB file through the public `solve_smtlib` front
door, and it was *introduced* by the increment being landed — absent from `main`
before the merge. Everything else below is secondary to that.

---

## 1. What landed

| Commit | What |
|---|---|
| `6ac79d19` | Operational records (multi-agent diary, four-agent review) committed; `.gitignore` closed for the access-controlled Glaurung capture and local CI logs |
| `4bf77dab` | The agent dispatch program + SMT-COMP 2025 parity targets |
| `c4689faf` | `gen-scoreboard.py --check` made real; the drift it was hiding corrected |
| `0bdc0b69` | Stale Lean complete-parity manifest regenerated |
| `bbe5628c` | **Phase 0 merge** — Noetzli QF_SLIA closure + frontier artifact isolation |
| *(this)* | **P0 fix** — wrong-`unsat` in the singleton-outer-source identity |

Deliberately **not** landed: `agent/smtlib/fp-ground-div` (ADR-0373) — see §5.

---

## 2. The P0

`exact_singleton_outer_source_identity` accepted

```
(= (str.replace (str.replace S a r) S X)
   (str.replace (str.replace S a S) S X))
```

without requiring `X` to be the same term as `r`. The identity holds only when
`X == r`: with `a` first occurring in `S` at index `i`, `replace(S,a,r)` cannot
contain `S`, so the left side is `S[0..i] ++ r ++ S[i+1..]`, while
`replace(S,a,S)` does contain `S` at exactly `i`, giving `S[0..i] ++ X ++
S[i+1..]`.

```smt2
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (not (= (str.replace (str.replace x "A" "") x "B")
                (str.replace (str.replace x "A" x) x "B"))))
(check-sat)
```

At `x = "A"` the sides are `""` and `"B"`, so this is satisfiable. Axeyum
returned `unsat`; **cvc5 1.3.4 and z3 both return `sat`.** Three further mutants
of the same shape behaved identically. All four are now pinned as
soundness-negative controls and all four now return `sat`.

**Why it slipped both existing gates** — this is the reusable lesson:

1. The exhaustive identity test instantiates the schema with **one
   `replacement` binding reused in both positions**, which is exactly the
   `X == r` case the matcher is permitted to accept. It validated the
   *mathematics*, never the *accept/decline boundary*.
2. The string differential fuzz generates `str.replace` **only with literal
   needle and replacement**, so it structurally cannot emit the nested-needle
   shape the matcher requires. The new routes were invisible to it.

That is the `a946f925` pattern restated: a corpus sweep plus a fuzz that cannot
generate the corner is not a soundness gate. The gate that *would* have caught
it — perturbing an accepted schema away from its side condition and brute-forcing
any survivor — did not exist. It does now for this matcher; generalizing it to
all 33 accepted identity schemas is tracked as follow-up work.

**Cost of the fix: none.** It is a strict tightening, and the four Noetzli
families exercising the route all use `X == r`.

---

## 3. Verification performed

**Decide-rate — exact reproduction.** Release replay of the complete fixed
1,880-file Noetzli population (`20190311-str-small-rw-Noetzli`) at 250 ms
internal / 750 ms outer:

> **1,880 / 1,880 decided — 26 SAT / 1,854 UNSAT / 0 unknown.**

Unchanged after the P0 fix. One row (`str-term-small-rw_610`) differed between
the two aggregate runs; it decides `unsat` **5/5 in isolation at the same
budget** and both oracles confirm `unsat`, so it is parallel-load jitter, not a
capability change — the same treatment STATUS already applies to load-sensitive
rows.

**Soundness — independent adjudication.** The population declares
`:status unknown` on **every** file, so the declared-status check is *vacuous*
and cannot support a soundness claim on its own. Adjudicated instead against two
independent oracles in both verdict directions — all 26 axeyum-SAT rows plus a
300-row UNSAT sample, 326 total:

| Oracle | Agreed | Timed out (10 s) | Contradicted |
|---|---:|---:|---:|
| cvc5 1.3.4 | 315 | 11 | **0** |
| z3 | 318 | 8 | **0** |

**DISAGREE = 0.** Five instances are decided by axeyum that neither oracle
decided within 10 s.

**Gates.** `corpus_regression`, `cargo test --workspace --lib`, and
`progress_frontier` all pass on the merged tree, and the tree stays clean
afterwards (see §4). All 82 `qf_slia_fixed_splice` tests pass. All ten
generated-artifact `--check` gates pass, and all 209 `axeyum-smtlib` integration
tests pass.

### `just check` is still red — for a pre-existing reason

**It was red before this session started, for two independent causes.** One is
fixed here (the stale Lean manifest, §4). The other is not mine and is not
fixed:

`quantified_bv_differential_fuzz.rs:1037`, test
`boolean_discharge_of_opaque_bv_closures_matches_z3`, negative-control branch
`(3, Ok(Sat(model)), SatResult::Sat)`: axeyum returns `Sat` with a model and z3
agrees `Sat`, but `check_model(&arena, &[assertion], model)` returns
`Ok(false)` — **the lifted model does not satisfy the original assertion.** That
violates the standing rule that every `sat` must be checkable by evaluating the
original term against the lifted model. The fuzz is driven by a fixed-seed LCG,
so it is deterministic, not flaky.

Verified pre-existing by building and running that test at `ffc466b4`, the
pre-merge baseline: **identical assertion, identical line.** This session touched
no quantified-BV or BV source at all — only `axeyum-smtlib` parse/lib,
`axeyum-solver/src/smtlib.rs` (the SMT-LIB text front door for strings), and test
files — and this fuzz builds terms directly through the arena rather than routing
through that front door.

It is a live wrong-`sat`-model class in quantified BV and is P0 under the
project's own rules. It belongs to the quantified-BV boolean-discharge path
(Lane A or Lane F). Because the fuzz is fixed-seed, the next step is cheap:
instrument the failing case index and width, dump the assertion and model, and
establish whether the model is *incomplete* (a symbol left unbound that
`check_model` treats as unsatisfied) or genuinely wrong.

**So this note does not claim a green `main`.** It claims: the two failures this
session was responsible for are fixed, one pre-existing failure is fixed, and one
pre-existing P0-class failure is now *identified, attributed, and reproducible*
rather than buried behind an earlier gate failure — the first `just check` never
reached it, dying earlier on the `axeyum-smtlib` test that sorts before
`axeyum-solver`.

---

## 4. Two gate holes found and closed

**`gen-scoreboard.py --check` was a silent no-op.** The script had no argument
parsing at all, so `--check` was ignored: it unconditionally rewrote
`SCOREBOARD.md` and exited 0. Anyone using it as verification got a false pass
*and* a dirtied tree. `gap-ownership.md` names this script as a **G0** owner
path — "stop documentation from overruling measurements" — so a verification
flag that verifies nothing is squarely a G0 defect. It now compares, reports to
stderr, exits 1, writes nothing, and runs inside `parity-docs`.

Adding it immediately caught the drift it had been hiding: the committed
frontier table read `bv_reduction | 30 | 30 | 0 | 34` while its own committed
source `bench-results/frontier/bv_reduction.json` records baseline 30,
frontier 40, decided to knob 40. **A real +10 capability gain had never been
reflected.** Nothing caught it — scoreboard regeneration was not in `just check`
and `check-parity-docs.py` does not cover that table.

**`just check` was already red on `main`.** `gen-lean-complete-parity.py --check`
runs inside `parity-docs` and had been failing since `fe8ba9af` (2026-07-25),
which edited `.github/workflows/ci.yml` — a file the manifest
content-addresses — without regenerating it. Regenerated here; no parity counter
moved.

This is the **eighth** commit whose sole purpose is regenerating that manifest.
It hashes volatile infrastructure files (`ci.yml`, `justfile`), so any CI or
gate edit invalidates it and the local gate then fails for a reason unrelated to
Lean parity. `db265b80` already made the CI-side check non-blocking, which stops
CI going red but leaves the local gate red — hiding the signal rather than fixing
it. Whether infrastructure files belong in a *parity* manifest's identity set
deserves an ADR rather than a ninth regeneration commit.

**Frontier jitter fixed at the source.** `progress_frontier` rewrote five
`bench-results/frontier/*.json` files on every run, so any gate touching it left
the tree dirty across the integration checkout and four worktrees, and someone
reverted it by hand before each landing. `AXEYUM_PROGRESS_FRONTIER_ARTIFACT_DIR`
(cherry-picked from `agent/smtcomp/full-preparation-live`) now redirects those
curves, with the historical location retained when the variable is absent, and a
test rejecting empty and relative values. Demonstrated: the gate run left the
tree clean.

---

## 5. Branch audit — the "stale duplicates" assumption was wrong

The working assumption was that the middle group of worktrees were stale
duplicates of work already on `main`. **Two of them are not.**

`git cherry` misleads in *both* directions: branches showing `+N` unmerged
patches often hold content `main` already has under a different patch-id, and
branches showing all-`−` can still differ because they retain code `main` later
*deleted*. The decisive checks were `git merge-base --is-ancestor`, the two-dot
`git diff main <branch>`, and a symbol scan asking whether each added identifier
exists anywhere in `main`'s **history** (`git log -S`).

All ten named branches exist on `origin` at identical SHAs, so worktree removal
cannot lose commits; the only real risk was uncommitted content, and there was
none of substance.

| Branch | Verdict |
|---|---|
| `agent/solver/qfslia-regex-length-next` | **HOLD** — 34 commits, none in `main`, +3,622 lines of QF_SLIA/regex decision procedures. Assessed **INTEGRATE-NOW**: measured conflict is 10 hunks / 4 files, 8 of them "both sides appended at the same offset"; the 889-line regex-membership half merges with **zero** conflicts. Uniquely moves Kaluza +262, PyEx +69, StringFuzz — all dual-oracle confirmed. |
| `agent/smtcomp/full-preparation-live` | **HOLD** — `full_capture.py` (693 lines) exists in `main` at no path; `full_readiness.py` hardening. Its Rust half is landed here; the rest belongs to Lane D. |
| `agent/solver/uflia-deadline-next` | **Resolved** — initially flagged, but its 6 unique source commits are the same work `uflia-main-next` re-ports. All 11 flagged symbols present post-merge. Safe to prune. |
| 5 × `s4-*`, `mbqi-seed111-ci`, `uflia-family-next`, 3 scratch, 3 `/tmp` | Safe to prune |

**Do not drop `stash@{0}`** ("main-checkout frontier bench WIP (pre-landing,
backed up)") — a single shared stash, unaffected by `git worktree remove`.

---

## 6. Why `fp-ground-div` did not land

ADR-0373's **soundness core is clean** — facts come only from top-level asserted
conjuncts (so refutation uses a subset of the assertion stack), it can only emit
`Unsat`, it correctly requires a checked `non_nan` precondition before
`nonnegative` (avoiding the trap that `(not (fp.lt x +zero))` is *vacuously
true* for NaN), and it admits **RNE only** with no subtraction and no mixed
signs, so the 2026-07-22 cancellation P0 class is structurally unreachable. A
1,800-case differential fuzz against z3 fired 86 times and agreed 86/86.

It is held on an **availability** defect. `normalize_source_fp_expr` expands
`let` eagerly by cloning, destroying the DAG sharing `let` exists to provide.
The guards are a *depth* cap and a node count applied only *after* full
materialization, but depth does not bound size: `k` nested lets each referencing
the previous twice give `2^k` nodes, and `k ≈ 62` fits under the depth cap.

| nested lets | file size | wall | max RSS |
|---:|---:|---:|---:|
| 20 | 649 B | 1.10 s | 1.1 GB |
| 22 | 709 B | 4.21 s | 4.3 GB |
| **24** | **769 B** | **19.1 s** | **17.3 GB** |

This happens at **parse** time, so the solver timeout does not apply — the
process would be OOM-killed, which a competition harness reads as an abort
rather than `unknown`. That violates the standing rule *"graceful `unknown`,
never OOM/crash … every solving path must degrade under a deterministic
resource bound."* Blast radius is **all logics**: the route runs unconditionally
and its eligibility gate requires no FP content, so every single-query
macro-free script — the common shape of QF_BV/QF_ABV BMC output — pays a full
clone of every assertion body.

**The obvious fix was attempted and is not sufficient.** The merge itself is
done and clean on `integration/fp-adr0373-20260728` (`0a37ef2b`) — the single
conflict is the `Script` field, resolved by keeping both. On top of it,
`SOURCE_FP_MAX_NORMALIZE_WORK` is now charged *during* construction (sized well
above the 512-node eligibility cap, so no currently-eligible script loses
capability) plus a `source_mentions_fp_add` pre-gate, with tests for both.

Measured under a 6 GiB `scripts/mem-run.sh` cap: **4, 8, 12, 16 and 20 nested
duplicating bindings now decline cleanly**, where 24 previously cost 19.1 s and
17.3 GB. But **24 still aborts on allocation**, from a 1,928-byte script.

Instrumentation localizes it precisely: the four small assertions normalize with
the budget essentially untouched (99,990 of 100,000 remaining), and the fifth
dies *inside* `normalize_source_fp_expr` **without ever returning** — so the
`checked_sub` charge is not on the path that allocates. Two concrete suspects,
in order:

1. `let mut extended = environment.clone()` runs at **every** `let` level and is
   never charged at all.
2. `environment.get(atom).cloned()` **materializes** the substituted subtree
   *before* the budget is charged for it. Charging must precede the allocation:
   look the value up, count its nodes, charge, and only then clone.

The committed test is deliberately capped at 20 bindings so it passes honestly
rather than appearing to prove a bound that does not hold. Do not raise that cap
or land the branch until 24+ declines.

> Process note: the first attempt to measure this OOM-killed the host, because
> two cargo invocations were run concurrently without `scripts/mem-run.sh`.
> `CARGO_BUILD_JOBS=1` bounds parallelism *within* one cargo, not across two.
> Every subsequent run was serialized and capped, which is why the failure above
> is a clean 6 GiB abort with a usable diagnostic instead of a dead machine.

---

## 7. Open follow-ups

1. Fix the exponential-`let` bound, then land ADR-0373.
2. Generalize the schema-mutation gate to all 33 accepted identity schemas, and
   widen the string fuzz generator to nested/symbolic needles plus `\u{…}`
   escapes and code points above `0xFF`.
3. Integrate `qfslia-regex-length-next` (regex-membership half first — it is
   conflict-free, highest value, and has the safest UNSAT arm); hold
   `exact_fixed_segment_overlap_conflict` until it has an exhaustive reference
   test.
4. `SourceStringSatProblem::replays()` is called only from tests; search and
   check share one evaluator. Also: the returned model binds internal
   `!source_sat!{i}` symbols rather than the user's string symbols, so confirm
   what consumer-side replay does with the 7 new SAT rows.
5. Pre-existing on `main`: `parse.rs` `.expect("a bounded ite needle must
   distribute")` can panic on adversarial input — a crash, not a wrong verdict,
   but it violates "`unknown` is a first-class result, never an error."
6. Duplicate `:named` bindings are silently rebound; harmless today, but the
   first route to key on S-expression identity turns it into a wrong verdict on
   non-conforming input.
7. Decide whether infrastructure files belong in the Lean parity manifest's
   identity set (ADR), rather than a ninth regeneration commit.
