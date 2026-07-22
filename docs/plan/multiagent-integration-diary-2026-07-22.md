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
