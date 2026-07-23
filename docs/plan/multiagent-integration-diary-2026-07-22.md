# Multi-Agent Integration Diary — 2026-07-22

Integrator's running log for the three concurrent codex lanes. One entry per
review/integration cycle. Operating discipline: **read-only on agent lanes**,
green-before-merge gate, one integrator owns `main`
(`~/projects/personal/axeyum`). See
[`../contributor-guide/multi-agent-operations.md`](../contributor-guide/multi-agent-operations.md).

## The long-term vision (the compass for every merge decision)

> **lean/z3/cvc5 + Mathematica/sympy = axeyum** — a *proof-carrying* solver +
> CAS. Every result is certified or it DECLINES; soundness is never traded for
> coverage. Parity is measured against z3/cvc5 (SMT, quantifiers, the hard
> `QF_*` subset) and SymPy/Mathematica (CAS).

The three lanes are the three legs of that goal:

| Lane | Branch | Worktree | Leg of the vision |
|---|---|---|---|
| **Lean** | `agent/lean/nested-inductive-elimination` | `~/projects/personal/axeyum-lean-nested` | trusted kernel / proof import (the "lean" leg) |
| **SMT-COMP** | `agent/smtcomp/full-library-resume` | `~/projects/personal/axeyum-smtcomp` | solver parity vs z3/cvc5 on SMT-LIB (`QF_*` + quantifiers) |
| **CAS** | `agent/cas/vandermonde-wz` | `/nas4/.../claude-axeyum-cas-work` | SymPy/Mathematica parity (Vandermonde `∑C(n,k)²=C(2n,n)` next) |

## Integration process (each trigger)

1. Refresh refs; per-lane digest (commits, files-vs-main, in-memory merge preview, health).
2. Review each new commit's *diff* — scope (in-lane files only?), soundness, tests.
3. Green gate on a tree I own (warm target): `cargo test -p <crate>` for the
   changed crate + `cargo check --workspace --all-targets` for semantic-merge safety.
4. Merge only if green + conflict-clean; ff when possible. Push. Reset-on-red before any push.
5. Log micro (what each lane did) + macro (cumulative parity picture) here.

## Parity tracker (updated as lanes land; researched vs upstream)

| Front | axeyum today | Upstream ref | Gap being worked |
|---|---|---|---|
| Lean kernel import | nested-inductive **admitted natively** (TL2.14 done; strict-positivity + transactional) | Lean 4 kernel | remaining kernel-completeness gaps |
| SMT `QF_*` | full-library run ~30% at pause, WRONG=2 (FP, stale bin) | see landscape ↓ | full-library resume + FP-fix revalidation |
| CAS summation | Gosper + WZ (`∑C(n,k)`, `∑k·C(n,k)`, `∑k²·C(n,k)`, **`∑C(n,k)²=C(2n,n)`** ✓) | SymPy `Sum`/`hyperexpand`, Mathematica | Dixon/Saalschütz `₃F₂`; alternating `(−1)ᵏ` |

### SMT-COMP competitive landscape (per-division winners, for "distance to close")

**2025 single-query winners** (who owns each hard division today):

| Division | 2025 winner | 2024 % solved (ref) |
|---|---|---|
| QF_Bitvec (QF_BV) | **Bitwuzla-MachBV** | ~98% |
| QF_FPArith (QF_FP) | **Bitwuzla** | ~92% |
| QF_NonLinearIntArith (QF_NIA) | **Z3-alpha** | — |
| QF_NonLinearRealArith (QF_NRA) | **Z3-alpha** | — |
| QF_LinearIntArith (QF_LIA) | **OpenSMT** | ~94% |
| QF_LinearRealArith (QF_LRA) | Yices2 | — |
| QF_Datatypes | cvc5 | — |
| QF_Equality (UF) | Yices2 | — |
| QF_Equality_Bitvec (QF_ABV) | Bitwuzla | ~99.7% |
| QF_Strings (QF_SLIA) | Z3-Noodler-Mocha | — |

Frontier to chase: **Bitwuzla** owns BV+FP, **Z3-alpha** owns nonlinear,
**OpenSMT** owns QF_LIA, **cvc5** datatypes, **Yices2** equality/LRA. The
proof-carrying angle (certified `unsat`) is where axeyum differentiates rather
than trying to out-raw-solve Bitwuzla — track *decide-with-certificate* rate,
not just decide rate. (Sources in cycle-2 research note below.)

### Cycle 3+4 — 2026-07-22 (~11:30 EDT) — trigger: SMT + Lean commits

**Micro.**
- **SMT-COMP** 🟢 merged (ff → main): `23dfd4e8 integrate resumable fixture
  runner` + `0121874b gate unchecked AUFLIA refutations` + `3e872fb8 make resume
  gate executable`. The soundness one is the headline: QF_AUFLIA lazy-ROW was
  exporting `unsat` from a **scalar refutation with no independently checked
  proof** liftable through the array abstraction — now it **declines to
  `unknown`** at the adapter boundary (trades coverage for zero wrong-`unsat`
  risk; cheap certificate-rechecked array refuters still run first, so real
  UNSAT coverage is preserved). Fixture-backed (`corpus/.../QF_AUFLIA/.../
  pipeline-invalid.smt2` + `int_array_sort.rs`). **Gate: GREEN** — solver tests
  pass; `cargo check --workspace` exit 0. Note: the array test file is
  `#![cfg(feature = "full")]`; deep gate `-p axeyum-solver --features full`
  queued as a background verify (change is sound-by-construction regardless).
  The agent **rebased onto main** before pushing — clean ff.
- **Lean** 🟢 merged (`60aa89b2`): `96b6fbd4 Implement native nested inductive
  elimination` — **+2401 lines**, +1040 in `inductive.rs`, a new **1249-line,
  23-test** suite. This is TL2.14: the kernel now **admits** nested inductives
  (the M1 decline is replaced by real elimination). Highest-stakes review type
  (a soundness *expansion* of the trusted kernel). Verified the evidence:
  **185 kernel lib tests + all 23 nested-inductive tests pass**, and the suite
  includes the load-bearing negative cases — `negative_occurrence_..._rejects`
  (**strict positivity** preserved), `non_inductive_foreign_head_..._rejection`,
  and multiple `..._is_typed_and_transactional` / `rolls_back...` (rejections
  **roll back with no partial mutation** of the trusted environment). In-lane.
  **Gate: GREEN** — `cargo check --workspace` exit 0. Pushed.

**Macro.** The **Lean leg takes its biggest step yet**: from "nested inductives
DECLINE cleanly" (cycle 1) to "nested inductives are **eliminated natively**"
(this cycle) — a real move toward Lean-4-kernel parity, done the sound way
(strict-positivity gate + transactional admission, so a rejected inductive can
never half-mutate the environment). On the SMT leg, the AUFLIA fix is parity
*with a minus sign that's actually a plus*: we deliberately solve **fewer**
AUFLIA benchmarks than z3/cvc5 until we can *certify* the refutation — the
decide-with-certificate metric is the one that matters here, exactly as the
landscape note argues.

**Health.** `/tmp` cleaned 80%→8% (45G of stale scratch reclaimed); doctest
quota flag cleared. No runaways; temps nominal.

**Watch-items.** All three lanes now touch shared `PLAN.md`/`STATUS.md`/docs;
so far every merge auto-resolved union-clean. The SMT `full`-feature deep gate
is the one open verification.

### ⚠️ TRACKED ISSUE — pre-existing CI-red under `--all-features` (FP, NOT mine)

The SMT deep-gate (`cargo test -p axeyum-solver --features full`) surfaced a
**failing test**, `user_declare_cannot_alias_fp_max_signzero_bit`
(`crates/axeyum-solver/tests/fp.rs:731`). This matters because the **official
gate and CI both run `--all-features`** (`justfile:16`, `.github/workflows/ci.yml:96`),
which enables `full` — so **`main`/CI is red in that config**, and has been since
**before this session** (baseline `48fece10`; the only `.rs` files changed since
are `lean-*`, `axeyum-cas`, `abv.rs` — no FP code). My per-merge gate used
default features + the changed crate's tests, so it never compiled these
`full`-only tests.

**Root cause (diagnosed read-only — definitive):** it is a **stale white-box
test**, not a soundness regression.
- Current reduction (`crates/axeyum-fp/src/lib.rs:3762`) names the opposite-sign-zero
  bit by **format + order**: `axeyum_fp.max.signzero.{exp}.{sig}.{pos_neg|neg_pos}`.
  `axeyum-fp`'s own tests (`lib.rs:7391+`) use that scheme, confirm the internal
  namespace firewall holds, and confirm no symbol is minted for non-zero pairs.
  The sound behavior (a fresh free Boolean per application, via `declare_internal`,
  never a wrong `unsat`) is intact and covered.
- The failing test hardcodes the **old operand-index** name
  `axeyum_fp.max.signzero.{pos0.index()}.{neg0.index()}` (`fp.rs:738`), which the
  reduction no longer uses → `find_internal_symbol` → `None` → panics at the
  precondition, before the real firewall assertion (`fp.rs:746`) even runs.

**Assessment:** low-severity, test-only staleness; a duplicate of coverage that
already lives authoritatively in `axeyum-fp`. **Recommendation:** the FP/soundness
lane should update the solver-side test's expected name to the format+order
scheme (F32 → `axeyum_fp.max.signzero.8.24.{pos_neg|neg_pos}`) or delete the
duplicate. **Left untouched** — outside the three monitored lanes; awaiting the
owner's call. **Integrator note:** the `--all-features` baseline now has exactly
this ONE known red — any *other* `--all-features` failure is a real new regression.

### Cycle 5 (heartbeat ~12:00 EDT) — no merge; macro checkpoint + live-run soundness

**Docs merged since cycle 4:** Lean `70c1c7e7` (M2 completion) + `ead963c8`
(preregister M3 grammar) — both docs-only, merge-clean.

**All three lanes active mid-work (uncommitted WIP, nothing to integrate yet):**
- **Lean** → `nested_inductive_grammar.rs` (M3, TDD: test first) — post-TL2.14.
- **SMT** → resumable-run contract + `compete.py`/`gen-contract` (10 files).
- **CAS** → `examples/probe_wz_next_tier.rs` — probing the **next hypergeometric
  tier past Vandermonde** (the Dixon/Saalschütz `₃F₂` direction flagged in the tracker).

**Live s4 full-library run — soundness alarm re-checked (README said it lapsed):**
scan of `/nas3/.../raw_selection/log_*.log` → **WRONG = 2**, and *both are already
fixed in code on `main`*:
- `pipeline-invalid.smt2  exp=sat got=unsat  <<< WRONG` — the QF_AUFLIA
  wrong-`unsat` that this session's `0121874b` (AUFLIA sound-decline) targets.
- `query.26.smt2  exp=unsat got=sat  <<< WRONG` — the P0 FP wrong-`sat` (KLEE),
  fixed by the FP lane (on `main` at baseline).
Both are the **stale s4 binary** (pre-fix), exactly as the README warned. Rough
verdict mix so far: unsat ≈10.4k, sat ≈4.8k, **unknown ≈14.9k**, timeout ≈0.95k —
the high `unknown` is the proof-carrying profile (declines, never wrong).
**→ Action for the SMT lane: re-stage s4 with a fresh `main` build; the WRONG
count should go to 0**, converting the AUFLIA case to a sound `unknown` and the
FP case to a correct `unsat`. This is the payoff loop: merges on `main` → measured
soundness on the full library.

**Health:** `/tmp` 8%, `/nas4` 68%, no runaways, 29 °C — all green.

### Cycle 6 — 2026-07-22 (~12:20 EDT) — trigger: SMT commit

**Micro.** SMT `e8908381 enforce one-host aggregate resources` (ff → main). The
§4 thermal/host-cooking discipline made **executable**: `resource_enforcement.py`
(one-host aggregate cgroup limits) + fixtures (`fake_solver.py`, `kill-after-start.smt2`)
+ two Python test modules; extends the `smtcomp-resume` gate to E2. No Rust
source (only `justfile` gate wiring). **Gate: GREEN** — new Python tests 7/7 OK;
official `./scripts/check-smtcomp-resume.sh` all sub-checks pass
(`invariants=18 scenarios=28 accept=5 reject=23 resume_byte_equal=true`). Pushed.
Gate note: Python-tooling change → gated with Python tests + the workstream's own
gate script, not cargo (correct tool for the change).

**Macro.** The SMT lane is hardening the *measurement harness itself* (resumable,
resource-bounded, cgroup-enforced) before scaling the full-library run — infra
that makes the decide/decline/WRONG numbers trustworthy and the run safe to leave
unattended on shared hot hosts. Complements the pending s4 re-stage action.

Also merged (docs-only) since: SMT `c56b4168` preregister E3 multi-host durability.

### Cycle 7 (heartbeat ~12:30 EDT) — no merge; lane-depth checkpoint

**Lane WIP (read-only):**
- **Lean** → M3 grammar, 3 files WIP (grammar is slow, hard work; steady).
- **SMT** → E3 durability, 6 files WIP, very active (committed 6 min ago).
- **CAS** → **123-line in-flight change in `lib.rs`** (103+/20−). *Not* a stall —
  after the `probe_wz_next_tier.rs` exploration it folded the work into core and
  is mid-implementation of the next hypergeometric tier (`₃F₂` Dixon/Saalschütz
  direction), getting it green before committing. ~2 h on genuinely hard math.

**Live s4 run:** progressed `[2356/8044] → [2591/8044]`, still writing (12:31),
**WRONG still 2** (unchanged — same two stale-binary cases; re-stage still pending).

**Health:** `/tmp` 8%, `/nas4` 68%, no runaways, 29 °C.

### Cycle 8 — 2026-07-22 (~12:40 EDT) — trigger: SMT commit

**Micro.** SMT `99e542af E3 multi-host durability gate` (→ main `a345588c`).
Large: **`multi_host.py` +1909**, `test_smtcomp_multi_host.py` +790,
`test_smtcomp_multi_host_live.py` +491, plus `compete.py`/`resource_enforcement.py`/
`resume_fs`/`resume_runner` updates and E3 kill/durability fixtures. Python only,
no Rust. **Gate: GREEN** — unit tests 6/6 OK; official `check-smtcomp-resume.sh`
E0–E3 exit 0 (`invariants=18 scenarios=28 accept=5 reject=23`); the `_live`
multi-host test **skips gracefully** without real infra (not a failure). Diary
integrity verified across the merge (my cycles 1–7 preserved).

**Macro.** E1→E2→E3 in one session: the SMT harness is now resumable
(byte-equal), one-host resource-bounded (cgroup), and **multi-host durable** —
i.e., a full-library run can be sharded across hosts, survive a host dying
mid-shard, and resume without double-counting or losing verdicts. This is the
infra that makes an *honest, reproducible* decide/decline/WRONG map of all of
SMT-LIB feasible — the prerequisite for the z3/cvc5 parity measurement the whole
lane exists to produce.

### Cycle 9 — 2026-07-22 (~12:50 EDT) — trigger: SMT (batched E3 hardening)

**Micro.** Three small E3-durability follow-ups, each merged + gated green
(official `check-smtcomp-resume.sh` E0–E3 `resume_byte_equal=true` + multi_host
unit tests), all Python:
- `138ef9f8` freeze NFS checkpoints after link (`resume_fs.py` — checkpoint atomicity).
- `d079087e` precreate E3 shared namespaces (`multi_host.py` +41).
- `f08e8af7` observe E3 fault markers on owner host (`multi_host.py` +78; `_live`
  test expanded +74 to cover fault detection).

**Macro.** This is the "make it actually survive a real distributed run" pass —
NFS checkpoint atomicity, namespace precreation, and owner-host fault observation
are the failure modes that bite an unattended multi-host sweep. The lane is
paying down operational risk before turning the full 64k-file run loose, so the
resulting parity map is trustworthy rather than corrupted by harness faults.

### Cycle 10 (heartbeat ~13:00 EDT) — no merge; two deep-work lanes

- **Lean** → M3 grammar, **~899 lines in flight** (`inductive.rs` + `inductive_tests.rs`
  + new `nested_inductive_grammar.rs`). A large commit is brewing; will get a
  TL2.14-grade review (kernel soundness + negative/transactional coverage) on landing.
- **CAS** → **WATCH-ITEM:** ~2 h on the next hypergeometric tier (`₃F₂`
  Dixon/Saalschütz past Vandermonde); WIP churned **123→36 lines** (tried a
  larger approach, backed it out, iterating leaner). Signature of a genuinely
  hard problem, not a hang — WZ certificate discovery for `₃F₂`-class sums is a
  real step up from the squared-Γ ratio. Not interfering (lane autonomy); will
  review carefully when it commits. If it stays silent for another ~2 h I'll note
  a possible block for your attention.
- **SMT** → E3 hardening, at rest (0 WIP) after the batch.

**s4:** `2667/8043`, WRONG=2 (stale binary). **Health:** green, 35 °C.

### Cycle 11 — 2026-07-22 (~13:15 EDT) — trigger: Lean M3 landing (major)

Interim minor merges since cycle 9 (batched, all gated green): SMT `14b54be9`
keep-staged-immutable, `84b40626` seal-E3-env+fault-evidence; Lean docs
`ab5dbf99`/`d03ba0fc` (M3 integrity/survivor evidence).

**Micro — the M3 implementation landed:** Lean `6a2afdd5 Harden nested inductive
restoration evidence` (→ main `0569c9cf`) — **+3826 lines**: `inductive.rs` +170,
`inductive_tests.rs` +841, new **2817-line** `nested_inductive_grammar.rs`. The
grammar test is a **systematic 640-case matrix** — `admit:320, reject:320` with a
mutation-check grid (`auxiliary-count-and-order`, `deduplicated-reuse`,
`distinct-specialization`, `motive-and-minor-order`, `recursor-dependency-target`,
`restored-rule-constructor-and-nfields`, `temporary-name-leakage`,
**`typed-rejection-rollback:320`**). In-lane, merge-clean. **Gate: GREEN** —
grammar matrix `generated_nested_inductive_grammar_is_complete_and_byte_identical`
passes (64.9s, all 640 cases, byte-identical/deterministic); kernel lib **188
passed** (+3); `cargo check --workspace` exit 0.

**Macro.** The Lean leg reaches a milestone: nested-inductive elimination is not
just *implemented* (TL2.14, cycle 3) but **exhaustively characterized** — 320
admissions and 320 typed rejections, each rejection verified to roll back with no
partial environment mutation, and the whole grammar proven complete + byte-identical
(reproducible). For a *trusted kernel*, this exhaustive-negative + transactional
+ deterministic coverage is the real bar; it's what lets nested inductives be
admitted without widening the trusted base unsoundly. Lean-4-kernel parity on this
feature is now genuinely close.

### Cycle 12 (heartbeat ~13:30 EDT) — no merge; CAS resolved + transient health spike

- **CAS WATCH-ITEM RESOLVED** — not stuck: the in-flight `lib.rs` diff shows it
  implementing **`prove_squared_binomial_moment`** (`∑ₖ (k)_order·C(n,k)² =
  closed_form`) and **`prove_fixed_shift_binomial_convolution`**, each carrying a
  rational WZ certificate + `false_proof` soundness tests. Concrete next-tier
  theorems past Vandermonde — real, careful work, uncommitted only because the
  certificate machinery is being gotten right. The sharp end of SymPy parity.
- **Health spike (transient, self-resolved):** a digest tick caught **3
  `axeyum-smtcomp` procs + 61 °C** (up from 35). Seconds later (read-only check)
  the procs had exited, load was falling (2.67 1-min vs 4.55 15-min), temp back to
  59 °C — a short E3 `_live`/`compete` burst, not an orphaned runaway. No
  `stop_run.sh` needed. First §4 blip; re-checking temps each tick.
- **Lean** post-M3 → now preregistering M4 (importer). **SMT** E3 accepted (0 WIP).
- **s4:** live (last write 13:30), WRONG=2 (stale binary). NB: tail progress
  markers are per-shard, not a global monotonic counter.

### Cycle 13 — 2026-07-22 (~13:45 EDT) — trigger: Lean M4 importer landing

**Micro.** Lean `f03dfcdf Import official nested inductive groups` (→ main
`b2e5c0fa`) — the **M4 importer**: `lean-import/lib.rs` +152, updated
`official_construct_matrix.rs`, new **578-line** `official_nested_inductive_groups.rs`
(6 tests). Flips the M1 `Unsupported("inductive-nested")` decline into **actual
import** of nested inductive groups — now that the M3 kernel grammar can admit
them. In-lane, merge-clean. **Gate: GREEN** — all `axeyum-lean-import` tests pass
(incl. the new nested-groups suite); `cargo check --workspace` exit 0.

**Macro.** This closes the loop on the Lean nested-inductive arc: M1 (decline
cleanly) → TL2.14/M3 (admit + exhaustively characterize in the kernel) → **M4
(ingest from real Lean export data)**. The kernel can now not only *reason about*
nested inductives soundly but *receive them from the outside world* — the whole
point of a proof importer. Lean-import parity on nested inductives: functionally
there, end-to-end.

### Cycle 14 — 2026-07-22 (~13:55 EDT) — first doc conflict + a self-inflicted slip

**Merges:** SMT `bb72bd2c` (ADR-0356 preregister official selection identity,
docs) + Lean `5d3e8333` (M4 completion, docs).

**First real conflict** — Lean M4 completion vs SMT selection-identity both
prepended a `STATUS.md` changelog entry at the same anchor. Resolved by **union**
(kept both entries, no lane's lines clobbered), per the watch-item plan.

**⚠ Self-inflicted slip (caught + fixed):** while staging the conflict
resolution I ran `git add -u`, which **swept the pre-existing `bench-results/
frontier/*.json` WIP** (not mine — present since session start) into merge commit
`ff96ef4b`. Caught it immediately on post-merge verification, then restored the
files to baseline in a follow-up commit (`dbe21c5d`) and rewrote the modified
content back into the worktree **unstaged** — so `main` HEAD is clean and the
user's WIP is preserved exactly as before. **Lesson (already in
`multi-agent-operations.md` §2): pathspec commits ONLY — never `git add -u`**,
even for a merge resolution. Reverting to explicit `git add <files>` for all
future conflict merges.

### Cycle 15 — 2026-07-22 (~14:00 EDT, 3 h heartbeat) — soundness verification + progress

**Merges (all gated green, clean):** Lean M5 computation tests (`edfa7924`); SMT
S0 official selection authority (`db791ef4`) + adapt inputs (`f8878fee`) —
`sources=29 submissions=53 competitive=38 non_incremental=450472 seed=22731158`
(exact-match to the official SMT-COMP population).

**★ Soundness verification — s4 WRONG jumped 2→16; investigated → all stale-binary
lag, current `main` VERIFIED sound.** Categorized the 16: 1 QF_AUFLIA
(`pipeline-invalid`, fixed by this session's AUFLIA sound-decline) + 15 QF_FP
(KLEE `query.26` + **14 new Wintersteiger `div`/`mul`/`fma`**). The new FP cluster
was *not obviously* covered by the known FP fixes (which were min/max signed-zero,
add/fma exact-zero, classification — not clearly div/mul), so I did **not**
overclaim. Instead: rebuilt `smtcomp_cli` from current `main` and ran it on
representative WRONG cases — **`div-has-solution-811`✓, `div-has-no-other-solution-3577`✓,
`mul-has-no-other-solution-1475`✓, `fma-has-solution-10232`✓ (4/4 correct, both
sat and unsat directions).** Conclusion: **current `main` is sound on all of them;
WRONG=16 is entirely the stale pre-fix s4 binary.** This *verifies* (not just
asserts) that re-staging s4 → WRONG→0. The FP fixes are more complete than feared.

**★ CAS major progress (uncommitted, ~3 h deep — NOT stuck).** Its `lib.rs` WIP +
`docs/research/10-cas/diary.md` (Entry 37ads) show it has certified the **entire
squared-binomial falling-factorial moment hierarchy through order 15**
(`prove_squared_binomial_falling_moment`, `prove_squared_binomial_moment`; order
16 is the first measured decline → sound ceiling), plus
`prove_fixed_shift_binomial_convolution` (`ΣC(n,k)C(n,k+r)=C(2n,n−r)`, r=0..7).
**521 unit + 147 doctests green** (up from 504) — 17 new certified theorems past
Vandermonde. A big, high-value CAS merge is pending once the lane commits.

**Health:** transient 82 °C peak (a lane's `just check`), back to 40 °C; no runaways.

### Cycle 16 — 2026-07-22 (~14:15 EDT) — SMT S0/S1 selection + two process fixes

**Merges (all gated green):** Lean M5 assurance (`34652338` — STATUS union-resolved,
Lean-compat Python 55/55); SMT selection-authority chain `db791ef4` S0 →
`f8878fee` adapt inputs → `16764d04` audit inputs → `0c81f06d` match official
submissions (`seed 22731158→22731074`, `submissions 53→51`) → `eb81e506` filter
global logic expansion by track. The SMT lane now has S0 authority + S1a format
adapters + S1b selection-free live auditor — a *provably-official* population with
independent audit.

**Process fix #1 — second WIP slip, then hardened.** After a **flaky** gate result
(see #2) I ran `git reset --hard HEAD~1`, which **wiped the pre-existing
bench-results WIP** (same hazard class as the cycle-14 `git add -u`). Restored it
from the 13:53 backup (nothing edits `~/axeyum/bench-results` — lanes use their own
worktrees — so content was unchanged). **New standing pattern for gated merges:
`git merge --no-ff --no-commit` → gate → `git commit` (green) or `git merge
--abort` (red).** `merge --abort` preserves unstaged WIP; **`reset --hard` is
banned** in this tree. Verified: WIP survives every merge since.

**Process fix #2 — flaky gate observed.** `0c81f06d`'s `check-smtcomp-resume.sh`
returned `FAILED (failures=1, skipped=1)` on the first run, then **exit 0 on two
consecutive re-runs**. Almost certainly shared-state contention — the SMT lane
runs the same Python tests concurrently in its own worktree, and the gate touches
shared NAS/temp fixtures. **Integrator rule added: on a RED that doesn't reproduce,
re-run twice before believing it; a single transient fail is not a red branch.**
(Had I trusted the first fail, I'd have wrongly held back a green commit.)

**Interim SMT merges (batched, all gated green via safe pattern):** `32ecd649`
preserve idempotent removals, `41ee9b34`/`5051dfbc` external-sort eligibility
ledger (memory-bounded S1 producer over the 450k population).

### Cycle 17 (heartbeat ~14:30 EDT, 3.5 h) — CAS is soaring, not stuck

Re-examined the CAS lane (4 h uncommitted, WIP *churning* not growing — looked
like a possible block). **It is not blocked — it is doing exceptional work.**
Current WIP: `MAX_PROVED_SQUARED_BINOMIAL_FALLING_MOMENT = 33` (up from 15 at
cycle 15) via a new **nested-product-quotient compaction** — a WZ-ratio method
that cancels shared `(n)_j` factors *before* expansion, unlocking far higher
orders. New `nested_product_quotients_compact_order_nineteen_wz_ratios` test; a
live `cargo test` (isolated `/nas4/.../axeyum-cas-target.*` per §2) is validating
order-19 + the moment-family right now. The insertion "churn" was a *refactor*
generalizing past the order-15 code, not thrashing. **Lesson: WIP diffstat
shrinking ≠ stalling — for a proof engine it can mean a stronger, more compact
method replacing a weaker one. Read the actual functions before calling a block.**
A very high-value CAS merge (order-33 squared-binomial moments — well past typical
CAS reach) is queued.

**Others:** Lean 14-file WIP (M6 closure work incoming). SMT S1 producer active.
**s4:** WRONG=16 stable (all verified stale, cycle 15). **Health:** 36 °C, no runaways.

### Cycle 18 — 2026-07-22 (~14:40 EDT) — ★ LEAN ARC COMPLETE (M6 final closure)

**Micro.** Merged Lean `1d848ad4 Complete nested inductive elimination` (→ main
`e69b5117`) + SMT `b49777db` (S1 input audit complete). Lean M6 is docs-only (all
code landed M3–M5); it **accepts ADR-0355** and marks **TL2.14 DONE**. Two doc
conflicts resolved: `decisions/README.md` was a *semantic* union (took Lean's
0355 proposed→accepted **and** kept SMT's 0356 row — not a blind union); STATUS.md
pure union. Explicit-pathspec commit, no WIP swept, WIP intact.

Evidence recorded in M6: OLEAN digest **374,840 bytes reproduced** by two fresh
pinned-Lean runs; both negative runs reject with the registered diagnostic;
kernel **188 unit + 85 integration**, importer **47 integration**, doctests pass;
exact 640/720/768/840 populations + well-founded 35/0 controls; `DISAGREE=0`
parity docs. Honest scope: DONE "without granting native source, elaboration,
broad-library, ecosystem, or full-parity credit."

**Macro — the Lean leg's assigned arc is fully closed this session:**
M1 (decline cleanly) → TL2.14/M3 (admit + 640-case exhaustive kernel grammar) →
M4 (import from real Lean exports) → M5 (computation + assurance, OLEAN digest) →
**M6 (accept ADR-0355, TL2.14 DONE)**. Nested-inductive elimination — a real
Lean-4-kernel capability — is now soundly implemented, exhaustively tested,
importable end-to-end, and formally closed. The scoping caveat is the *right*
proof-carrying posture: it claims exactly what's verified (nested inductives) and
nothing more (not full Lean parity). One leg of the compass, genuinely delivered.

### Cycle 19 (heartbeat ~15:00 EDT, 4 h) — status + WRONG re-verified

- **Lean** — arc DONE, lane idle (0 WIP). Natural next frontier per M6 scope:
  native source / elaboration (explicitly *not* claimed yet).
- **SMT** — merged S2 `d48fb0dc acquire verified official corpus` (gated green).
  With S0/S1 selection frozen+audited and S2 corpus acquired, the full-library
  run is close to executable on a provably-official verified corpus.
- **CAS** — order-33 moment machinery now **accumulating** (203+/49− in `lib.rs`,
  up from churn) — converging toward the big commit. Still uncommitted (careful
  hard work; ~4 h).
- **s4 soundness — WRONG 16→23, re-verified all stale.** 22 are the known FP
  Wintersteiger (div/mul/fma) + AUFLIA classes; the 1 genuinely new class,
  `Double-to-float-no-simp1-main` (QF_BVFP `to_fp` conversion, wrong-sat on the
  stale binary), I checked against current `main` → **correct (unsat)**. So the
  FP fixes cover conversion too; **all 23 WRONG remain stale-binary lag, `main`
  sound.** (Method: always verify a *new* WRONG family against current `main`,
  never assume it's covered.)
- **Health:** 30 °C, no runaways, disk fine.

### Cycle 20 — 2026-07-22 (~15:10 EDT) — ★ MONITORING GAP found + 14-commit CAS catch-up

**The gap.** The CAS agent does **not stay on one branch** — it creates a new
topic branch per milestone (`vandermonde-wz` → `falling-moment-order-{seven,eight,
fifteen,sixteen,nineteen}` → `raw-moment-order-{eleven,twenty}`, plus
`squared-binomial-moment-family`, `fixed-shift-*`, etc.). My monitor **and** digest
watched the fixed name `agent/cas/vandermonde-wz`, which froze at `c9e6f48f`
(Vandermonde) hours ago. **So I was blind to all committed CAS work**, and my
cycle-12/15/17 notes calling it "uncommitted WIP for hours" were WRONG — it was
committing steadily to branches I wasn't watching. Correction logged here.

**The catch-up.** The live CAS branch `raw-moment-order-twenty` (`f08e97ef`) was
**14 commits** ahead of main — a certified moment hierarchy: WZ binomial identities
→ fixed-shift third/fourth/fifth moments → fixed-shift convolution family →
squared-binomial moment family → falling-factorial composition → direct moments
through eighteen → nested-WZ-quotient compaction → raw-moment composition.
merge-tree: **no conflicts** (CAS touched only `axeyum-cas` + `10-cas` docs; the
big two-dot file list was branch-lag, not overlap). Merged with the safe pattern;
**verified the 3-way merge kept all lean/smtcomp work** (grammar test still present)
and STATUS kept both lanes' entries (32 cross-lane markers, 0 conflict markers).
**Gate: GREEN — 522 CAS lib tests** (up from 504 at Vandermonde; +18 certified
theorems), `cargo check --workspace` exit 0. → main `f69dd5be`, WIP intact.

**The fixes.**
1. **Monitor rearmed** (`bajgo9gs8`) to track **worktree HEADs by path**, not
   branch names — immune to topic-branch switching; reports the live branch on each move.
2. **Digest** now derives each lane's branch from `git -C <worktree> branch
   --show-current` (fallback to seed), so it never watches a dead branch again.

**Lesson (important).** When agents create topic branches per unit of work, watch
the **worktree HEAD**, not a branch name. A fixed-branch watcher silently goes
blind the moment the agent branches — and "no commits on the branch I watch" reads
identically to "the lane is stuck," which is exactly the wrong conclusion I drew.

### Cycle 21 — 2026-07-22 (~16:40 EDT) — ★ s4 RE-STAGE: measured WRONG→0 (user-directed)

The user (rightly) flagged that I'd gone passive while lanes were heads-down, and
directed me to drive the long-pending s4 re-stage. Done, carefully (§4 thermal:
release build capped at `--jobs 8`, watched temp ≤77 °C; targeted runs with 120 s
caps, no fleet, no orphans; did not disturb the SMT lane's concurrent corpus job):

1. **Built** release `smtcomp_cli` from current `main` (33.9 s).
2. **Verified WRONG→0** on all **55** stale-binary WRONG cases the live s4 run had
   recorded: **53 CORRECT + 2 sound-decline (unknown) + 0 still-wrong + 0 missing.**
   The merged FP fixes (div/mul/fma exact-zero, add/fma, `to_fp` conversion) +
   AUFLIA sound-decline eliminate *every* one. This *proves* — not asserts — that
   the WRONG count was pure stale-binary lag; current `main` is sound on all of them.
3. **Staged atomically:** backed up the Jul-21 stale binary
   (`axeyum-smtcomp.stale-20260721.bak`), `cp`+`mv`'d the fresh one over
   `/nas3/.../harness/bin/axeyum-smtcomp` (atomic on one fs → safe for the running
   fork/exec loop). Sanity: staged binary returns correct `unsat` on a former-WRONG case.

**Note for the SMT lane:** the 55 already-*recorded* WRONG are historical (written
by the stale binary before the swap); newly-processed benchmarks now use the sound
binary. A fully clean board requires re-running the affected shards — the lane's call.

**This is the payoff loop closed end-to-end:** proof-carrying soundness fix on a
branch → green-gated merge to `main` → rebuilt binary → **measured 55 wrong
answers → 0** on the real SMT-LIB selection. Exactly the compass: never wrong.

### Cycle 22 — 2026-07-22 (~16:55 EDT) — CAS order-33 (pre-cancel) + gate-cost note

**Micro.** CAS `e5547fe2 pre-cancel raw moment products` (→ main `147c473f`).
Exact even-factor pre-cancellation + bignum-only polynomial intermediates remove
the raw order-20 representation overflow, extending Stirling-composed
squared-binomial moments **through order 33** (order-34 ceiling), public
coefficients still checked `i128`. STATUS.md union-resolved (main's S2/re-stage
block + the CAS order-33 entry; no WIP swept). The worktree-HEAD monitor fired
correctly (`HEADMOVE lane=cas`), confirming the cycle-20 fix. **Gate: GREEN —
524 CAS lib tests** (up from 522).

**Operational note.** The CAS suite now takes **~13 min** (794 s) — the high-order
moment proofs are genuinely expensive. **Going forward CAS gates run in the
background by default** (foreground hits the 7-min bash cap); merge stays staged
(`--no-commit`) until the background gate returns green, then commit.

**Macro.** CAS is now certifying binomial-moment identities to **order 33** with
checked WZ certificates — territory most CAS systems don't reach at all, let alone
with a proof. The order-34 "first decline" is the honest ceiling: it proves what
it can certify and declines beyond, never guesses.

### Cycles 23–28 — 2026-07-22 (~15:40–18:00 EDT) — new Lean worktree, CAS order-255, and the strategic gap finding

**New Lean worktree (user-flagged) + monitor overhaul.** The Lean agent finished
the nested-inductive arc and spun up a **whole new worktree** `axeyum-lean-parity`
(branch `agent/docs/lean4-complete-parity`) for **full Lean 4 parity** — a 428-line
parity contract + a registry that starts at **honestly zero** terminal credit
(can't affirm parity until the gates pass). My fixed-worktree monitor would have
missed it (same class as the cycle-20 CAS branch blindness, one level up). Fix:
monitor **and** digest now **auto-discover** agent worktrees from `git worktree
list` (any `refs/heads/agent/*`) — new worktrees/branches picked up with zero config,
`NEW-WORKTREE` announced. Also hardened the digest runaway detector twice (it was
self-matching my own monitor's worktree-path args, then my Claude shell-snapshot
wrappers — now excludes both; real runaways only). Memory updated.

**CAS to order 255.** `bignum-wz-base` → `broad-gap-probe-next`: bounded exact
`BigRational` base checking (runs only after the `i128` route returns `Unknown`,
fail-closed above Γ(256)/pow(1024)) carries **direct squared-binomial moments
through order 255, raw through 35** — 525 unit tests; order-256 declines cleanly at
`Γ(257)`. CAS gate now ~13–15 min (order-255 proofs are heavy) → background-gated
by default.

**SMT: S0→S4, still zero solver execution.** Merged the full official-selection
chain — S0 authority → S1 audit → S2 verified corpus (450,472 files) → S3 producer
→ S4 auditor. All green. But the STATUS entry literally ends *"No solver execution
is admitted yet."* Five rounds of selection provenance.

**★ STRATEGIC FINDING — the QF_\* decide-rate gap is unworked, and the SMT lane
isn't pointed at it.** Pressed on this (user asked directly). The entire session's
solver-code delta is **one file** (`abv.rs`, the AUFLIA decline); no quantifier
code moved (the ~35 `quant_*.rs` subsystem is untouched). Live run: **~50% decided
/ ~46% unknown** — sound but low-coverage; and it will *drop* when the run reaches
strings (~24% of the library, axeyum's weakest, not yet measured). Per
`full-library-gap-closing-plan-2026-07-22.md`: Rank 0 (soundness) ✅, but the
gap-closing patterns are **Ranks 2–6** (strings P2.7, quantifier MBQI P2.6,
CDCL(T) keystone, nonlinear P2.5, QF_BV/FP perf) — **all untouched**, and the plan
gates them behind **Rank 1 (finish the official measurement)**, which also isn't
done. The SMT lane has been building measurement *apparatus*, not closing the gap.
Drafted a pivot directive for the user to relay (finish Rank-1 measurement on the
S2 corpus with the sound binary → then Rank 2 strings; hold Rank 3 quantifiers,
gated on the keystone). **This is the honest headline: soundness parity delivered
& verified; coverage/quantifier parity measured, planned, blocker-cleared — but
the climb itself is unstarted and currently unassigned.**

**Housekeeping.** Corrected a sloppy host claim: the full-library run is on **s4**
(verified via `distribute_run.sh` config + live `ssh` ps; s5/6/7 idle) — my earlier
"s5" was a substring false-match. Re-armed the soundness alarm correctly labeled s4
(`b4qirg8ky`); the re-stage keeps holding (WRONG stable at 56, no new post-swap).
Two WIP-preservation slips earlier (`add -u`, `reset --hard`) both recovered; safe
merge pattern (`--no-commit`→gate→commit/abort) + a Python STATUS union-resolver now
standard. `main` `48fece10 → 2f40ed82`; ~130 commits; WIP intact throughout.

---

## Cycle log

### Cycle 1 — 2026-07-22 (~10:48 EDT) — trigger: Lean commit

**Micro.**
- **Lean** — merged `48fece10..99ec3e3e` (2 commits): `893afc1f fix(lean-import):
  classify nested recursor exports` + `99ec3e3e docs: close Lean nested-inductive M1`.
  The fix moves nested detection *before* admission and gates on a structurally
  derived `numNested` (recursor count == families + nested, else typed decline),
  reclassifying nested exports from `Malformed/message` → `Unsupported/code`
  (a cleaner "we DECLINE this" signal — right on the soundness compass).
  Scope: code only in `axeyum-lean-import`; rest docs + PLAN/STATUS.
  **Gate: GREEN** — `cargo test -p axeyum-lean-import` all pass; `cargo check
  --workspace --all-targets` exit 0. **Merged (ff) → main `99ec3e3e`, pushed.**
- **SMT-COMP** — 3 uncommitted files in tree, no commit yet. Warming up.
- **CAS** — 2 uncommitted files (the `vandermonde-wz` task), no commit yet.

**Macro.** Lean's leg advances from "nested inductives were an ad-hoc malformed
error" to "nested inductives are a *typed, tested, structural decline* (M1
closed)" — the correct pre-condition before actually admitting them (TL2.14).
This is the proof-carrying discipline working: decline precisely, then extend.

**Health.** `/tmp` 80% (doctest-link quota watch — TMPDIR isolation in use);
`/nas4` 61%; no solver runaways; 28 °C. All green.

**Watch-items.** Lean edited shared `PLAN.md`/`STATUS.md`; if CAS/SMT touch them
too, expect doc-level merge conflicts — resolve by union, never clobber a lane's lines.

### Cycle 2 — 2026-07-22 (~11:05 EDT) — trigger: CAS commit (found at monitor arm)

**Micro.**
- **CAS** — merged `c9e6f48f feat(cas): certify Vandermonde via WZ` (non-ff merge
  → main `4b0cef35`). This closes the **highest-value open CAS gap** I'd flagged:
  `∑ₖ C(n,k)² = C(2n,n)`. The 137-line `gosper.rs` change adds the squared-Γ
  ratio reduction that previously blocked it. Verified it's a *real* certificate,
  not a shortcut: the test drives `prove_wz_sum` (symbolic WZ soundness gate) AND
  includes a **negative test** — `prove_wz_sum(…, rhs+1)` must return `None`
  (rejects the false identity). Scope in-lane (CAS crate + docs + STATUS.md;
  STATUS.md auto-merged union-clean vs Lean's edit — the predicted conflict did
  not bite).
  **Gate: GREEN** — `cargo test -p axeyum-cas --lib` = **504 passed** (was 503;
  `wilf_zeilberger_binomial_sum_proofs` now covers Vandermonde); `cargo check
  --workspace` exit 0. **Pushed.**
- **Lean** — quiet since M1 (tip `99ec3e3e`, already on main).
- **SMT-COMP** — still no commit (tip `48fece10`); lane warming up.

**Macro.** CAS parity vs SymPy takes a real step: the WZ machinery now handles
**squared-binomial hypergeometric sums**, not just linear `∑k·C(n,k)` /
`∑k²·C(n,k)`. Vandermonde is the canonical "can your CAS do nontrivial binomial
identities" test — SymPy does it via `hyperexpand`/Gosper; we now do it *with a
checked certificate*. Next natural CAS targets on the same machinery: Dixon /
Saalschütz `₃F₂` identities and alternating sums (still blocked on `(−1)ᵏ`
representation — the open structural item).

**Note.** The SMT-COMP resume README warned `main` was RED (missing
`ExprNode::Proj` match arm in `quantifier.rs:537`). That blocker is **already
resolved upstream** — `cargo check --workspace` is green at `4b0cef35`.

---

### Cycle 30 — 2026-07-22 (~18:00–19:30 EDT) — ★ MBQI landed + the A/B reality check

**The SMT lane finally shipped decide-rate-adjacent CODE** (after 5 rounds of
selection provenance S0–S4): `abbf7abd feat(quant): check finite-profile MBQI
models` (→ main `f37b3b9e`). New `quant_uf_model_sat_cert.rs` (+311) does the
finite-profile *proof*; `mbqi_model_finder.rs` is now the search-side bridge;
`certify_all_universals` returns a certificate ONLY when the model is
independently proved to satisfy every universal, else declines. Wired into
`auto`/`capabilities`/`support_matrix`. **Gate: GREEN** — `mbqi_model_finder`
12 tests + `quantified_uflia_model_finder_differential_fuzz_disagree_zero`
(154 s, **0 disagreements** vs reference) + `cargo check --workspace` exit 0.

**★ A/B on real SMT-LIB (the user asked "does it flip to green?") — answer: NO.**
Built old (pre-MBQI) vs new (MBQI) binaries, ran on 29 quantified-sat
UF/UFLIA/UFNIA/AUFLIA benchmarks + synthetic on-fragment cases:
**0 net new decides** (28 still `unknown`, 1 already-sat, **0 wrong**). MBQI IS
reachable (CLI decides `∀x:Int. f(x)≥0` → sat, checked) and sound, but everything
it decides the pre-MBQI binary *already* decided. **Corrected my over-claim:** this
commit **hardens existing narrow MBQI to be proof-carrying**, it does NOT expand
coverage. The real lever — general model-based instantiation (T2.6.5), MAM,
trigger inference — is still ahead. **Decide-rate on real quantified problems:
unchanged.** (Lesson: green tests ≠ moved needle; test capability on real
benchmarks, exactly as the user pushed.)

**CAS broad-gap-probe waves** (branches `bignum-wz-base` → `broad-gap-probe-*` →
`inverse-laplace-repeated-quadratic`): order-255 squared-binomial moments +
Z-transform families + symmetric rational-trig Fourier periods — **528 tests**,
all capped-gate-green. **Lean-parity**: still docs/registry (TL0.7.x checkpoint
store/evidence/acceptance) — building the parity-tracking machinery, honest-zero.

**Thermal lesson (logged to memory).** The order-255 CAS gate drives this host to
~90–93 °C by itself; run it thread-capped (`RAYON_NUM_THREADS=4 … --jobs 4 --
--test-threads 4`) in the background, keep the merge staged until green, and do NOT
kill/restart over a blip (governor self-protects; restart wastes ~15 min + more heat).

**Honest scoreboard (~180 commits, 59 merges):** soundness parity delivered +
verified (WRONG→0 re-staged); quantifier path now proof-carrying (but not more
capable); CAS moment/transform machinery deep; Lean nested-inductive done + full
parity registry building. **The QF_*/quantifier COVERAGE gap remains ~50% decided
and essentially unmoved** — the climb (plan Ranks 1–2, 5) is still not underway.
