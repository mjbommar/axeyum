# 2026-09-16: sizing a model-preference policy (items 6, 7, 9 of the 2026-09-16 list)

Lane AX-POLICY, step 0 of ADR-2140. Everything below is a `file:line` read of
the tree at `8df853252`, taken before any code was written, so that the ADR's
design rests on what the SAT core does rather than on what its module docs say
it does.

## The question

Two consumers want to choose WHICH model a `sat` returns: Glaurung measured
that 79 % of both-sat queries returned different valid models between z3 and
Axeyum (`docs/history/axeyum-integration-2026-07/PAPER-NOTES.md:215` in the
Glaurung tree, read-only), and `python/examples/cindergraph_defects/check.py`
re-solves under growing magnitude bounds (`BOUNDS = (1, 16, 256, 4096)`,
`check.py:56`; `bounded()` at `:76`, `solve()` at `:90`) to get a witness a
reader can check by hand — up to five solves per finding.

## Where a decision polarity is chosen

| what | where |
| --- | --- |
| The decision literal's polarity | `crates/axeyum-cnf/src/proof_sat.rs:3518` — `if self.phase[var] { positive } else { positive.negated() }` |
| Phase saving (every assignment overwrites `phase[var]`) | `proof_sat.rs:3158`, in `enqueue` |
| The initial polarity | `Cdcl.initial_phase`, `proof_sat.rs:2059`; default **`false`** at `:2446`; `phase`/`best_phase` grow with `false` at `:2536-2537` and `target_phase` with `initial_phase` at `:2538` |
| Restart-time target rephase (`phase := target_phase`) | `proof_sat.rs:3443-3445`, gated on `use_target_rephase` (default `true`, `:2449`) |
| Scheduled rephase (`Best` / `Inverted` / `Original`) | `proof_sat.rs:3113-3131` (`apply_rephase`); the schedule is `PhasePolicy`, `crates/axeyum-cnf/src/phase_policy.rs:130`, and the shipped default is `PhasePolicy::pinned()` (`proof_sat.rs:628`), under which `should_rephase` never fires |
| One-shot entry the BV backend uses | `proof_sat.rs:510` `solve_with_drat_proof_with_limits(formula, deadline, max_conflicts)` — no options parameter; `Cdcl::new` then `solve` |
| Warm entry the incremental engine uses | `crates/axeyum-cnf/src/proof_sat/incremental.rs:583` `NativeIncrementalCdcl::solve_within`; `initial_phase` honoured for caller-declared variables at `:452-466` (`grow_to`) |
| The CDCL(T) knob that already exists | `TheorySolveOptions::initial_phase`, `proof_sat.rs:1229` (default `false`, `:1286`; `native_cdclt.rs:621` sets `true`) |

**Finding 1: the pure Boolean core already decides `false` first.** The
shipped QF_BV path (`initial_phase = false`, `PhasePolicy::pinned()`) starts
every variable at `false`, so "initial phase all-false" is *today's
behaviour*, not a new policy. What moves a symbol bit to `1` in a returned
model is either propagation (the constraints force it) or **phase saving**: a
bit assigned `true` inside an earlier, later-retracted branch keeps `phase =
true` and is decided `true` the next time it is decided (`:3158`). Target
rephasing (`:3443`) re-installs the deepest conflict-free assignment on every
restart, which preserves whatever polarities that dive had.

**Finding 2: a preference that differs from today therefore has to override
phase saving, not the initial phase.** That is exactly z3's `phase=always_false`
(`references/z3/src/sat/sat_solver.cpp:1717-1741`, `guess()`: `case
PS_ALWAYS_FALSE: return false;` — the saved `m_phase[next]` is consulted only
under `basic_caching`/`caching`) and CaDiCaL's `forcephase`. cvc5 has no global
equivalent; its MiniSat carries a per-variable freeze bit
(`references/cvc5/src/prop/minisat/core/Solver.h:790-791` `setPolarity` /
`freezePolarity`, read at `Solver.cc:732-734`) that pins one variable's decision
polarity regardless of phase saving, which is the same mechanism scoped per
variable.

**Finding 3: it can be added without changing the search otherwise.** One
`Option<bool>` on `Cdcl` consulted at `:3518` only (and mirrored into the
`note_decision` argument at `:3533`): `None` leaves the branch byte-identical
to today; `Some(false)` decides every variable `false`. Propagation, conflict
analysis, restarts, the clause database, and the DRAT stream are untouched;
what changes is the trajectory, and therefore the *time* — which is what the
A/B in ADR-2140 measures. A verdict cannot change: `sat` still replays against
the original terms (`SatBvBackend::check_with_replay`, and the warm engine's
`replay` phase), and `unsat` still carries the proof it always did.

## How `SolverConfig` reaches the SAT core

| route | path |
| --- | --- |
| One-shot | `auto.rs` builds `SatBvBackend::new()` (`auto.rs:8554` for the QF_BV tail, `:6726`, `:9605`, `:10765`, …) and passes `config` at check time → `sat_bv_backend.rs:86` `check_with_replay(…, config)` → `:2327` `primary_sat_search(config, formula, deadline, …)` → `:2426` `solve_with_native_cdcl(formula, deadline, config.resource_limit, config.prove_unsat, reduction)` → `proof_sat.rs:510`. Only `resource_limit` and `prove_unsat` cross into the core today. |
| Warm | `incremental.rs:835` `IncrementalBvSolver::with_config(config)` keeps `config` (`:798`) and builds `IncrementalCnf::new()` (`:839`) with **no** config → `axeyum-cnf/src/lib.rs:698` `IncrementalSat { solver: NativeIncrementalCdcl }` → `proof_sat/incremental.rs:173` `NativeIncrementalCdcl::new()`. `timeout`, `resource_limit` and `preprocess` are consulted per check (`incremental.rs:832-834`); nothing else reaches the core. |
| Front door | `smtlib.rs:3713` `run_session(script, config, policy)` clones `config` into `effective` (`:3702`) and rebuilds it on every `set-option` (`:3843-3851`, only `:timeout` is folded in); `check-sat` calls `solve(&mut script.arena, &stack, &effective)` at `:3763` (`crate::auto::solve`). The honoured option set is `SessionOptions` (`:3533-3548`, five fields) and `apply_set_option` (`:3913`); anything else is `unsupported` (`:3941`). |
| Python | `crates/axeyum-py/src/solver/core.rs:670-677` `Incremental.__new__` resolves a `Config` into `SolverConfig` and calls `with_config`; `stats()` at `:741-756` returns a `dict` of 11 keys (not typed, not on `axeyum.smt`); `smt.solve` at `crates/axeyum-py/src/smt.rs:270` builds its config in `script_config` (`:398`). |

So the plumbing for item 6 is: a `model_preference` field on `SolverConfig`
(`backend.rs:113`), read (a) in `solve_with_native_cdcl` and handed to a new
`solve_with_drat_proof_with_limits_and_phase`, and (b) in
`IncrementalBvSolver::with_config`, handed down through
`IncrementalCnf`/`IncrementalSat` to a `NativeIncrementalCdcl::set_forced_phase`.
Both are additive; the `None` arm is the existing call.

## What `LeastUnsigned` needs beyond the phase

The core cannot express "smallest" — it decides bits, not words, and a decided
`false` on a gate output is not a decided `false` on a symbol bit. The example's
ladder is the honest mechanism: re-solve under `x ∈ [-b, b]` (two's-complement
magnitude; the wrap witnesses the brief names, `a = 0xFFFFFFFF` and
`len = -1`, are magnitude 1 and unreachable under an unsigned bound) for
`b ∈ {1, 16, 256, 4096}`, first `sat` wins, else the unbounded model. An exact
minimum already exists as `crate::optimize::minimize_bv` (`optimize.rs:1103`,
unsigned) and `minimize_bv_signed` (`:1219`), one objective at a time; the
ladder is one bounded solve per rung over *all* symbols at once, which is what
a witness-for-a-reader wants and what the example pays five solves for today.

## The registry

`AXEYUM_MODEL_PREFERENCE` has to be a registered `env_override`
(`config_registry.rs:11115` `every_env_override_is_read_by_the_code` — the
quoted literal must be read somewhere under `crates/`), and the entry must name
a live `const` (`:10412`); an enum-valued constant is matched by the textual
`const NAME:` fallback (`:10437-10444`) because `scan` (`:10281`) only parses
scalar and `Duration` types. `backend.rs` is not in `GOVERNED_FILES`
(`:9521`), so the new constant will not be demanded, only permitted.

## Sizing

| item | touch | new code | tests |
| --- | --- | --- | --- |
| 6 policy | `backend.rs`, `proof_sat.rs` (+1 field, +1 branch, +1 entry fn), `proof_sat/incremental.rs` (+setter), `axeyum-cnf/lib.rs` (+2 setters), `sat_bv_backend.rs` (+1 arg), `incremental.rs` (+1 line), `smtlib.rs` (+1 option), `config_registry.rs` (+1 entry) | ~150 lines | identity (corpus QF_BV, `Any` vs default), determinism (twice), replay under every policy, option parse |
| 7 ladder | `smtlib.rs` (+1 pub fn), `axeyum-py/src/smt.rs` (+1 pyfunction) | ~120 lines | the two defect shapes; bound reported; fallback to unbounded |
| 9 stats | `axeyum-py/src/solver/core.rs` (typed class), `axeyum-py/src/smt.rs` (re-export), stubs | ~80 lines | Python: fields present, monotone across two checks |
| A/B | script under `bench-results/` | — | 200 files, 2 arms, movers ×3 |
