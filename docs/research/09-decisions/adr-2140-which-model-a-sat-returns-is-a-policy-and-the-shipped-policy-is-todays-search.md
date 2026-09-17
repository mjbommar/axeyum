# ADR-2140: which model a `sat` returns is a policy, and the shipped policy is today's search

Status: proposed
Index-summary: Two consumers want to choose WHICH model a `sat` returns — Glaurung measured 79 % of both-sat queries returning different valid models between z3 and Axeyum and wants a least-unsigned witness for concretization, and the cindergraph defects example re-solved under growing magnitude bounds by hand, up to five subprocess solves per finding, to get a witness a reader can check. One mechanism now serves both: `ModelPreference { Any, PreferZero, LeastUnsigned }` on `SolverConfig`, plus `solve_smtlib_least_witness` — the bounded re-solve ladder `1, 16, 256, 4096` in two's-complement magnitude, first `sat` wins, else the unbounded model with the bound reported — behind `(set-option :model-preference …)`, `AXEYUM_MODEL_PREFERENCE`, and `axeyum.smt.least_witness`. **Two findings decided the shape.** The sizing found that the pure Boolean core ALREADY decides `false` first, so a "prefer zero" that differs from today must override phase saving (z3 `phase=always_false`); that override was wired to both SAT cores and MEASURED: it moved **0 of 15** corpus models (the search decides Tseitin gate variables, whose `false` propagates `1`s into inputs through negated AIG edges) and on the QF_BV pinned list cost **+27 % wall** on the both-decided files with 1 stable gain against 1 stable loss. So `PreferZero` finishes on the LIFTED model instead — a replay-checked greedy bit-clearing pass bounded by what the solve spent — which moves models (1 of 9 committed `sat` fixtures, the one with a free choice), costs **+12 %** with 0 gains / 0 losses / 0 flips / 0 `:status` disagreements, and replays 52 of 52 independently; the SAT-core phase ships OFF behind `AXEYUM_MODEL_PREFERENCE_PHASE=on`. `Any` is byte-for-byte today's search and stays the default: the identity test over every committed `QF_BV` fixture (43 compared) dies on a moved default, and a second test proves it can fail. Item 9 lands beside it: `Incremental(profile=True).stats()` is a typed `IncrementalStats` whose `profiled` field says whether its timers mean anything, because the Rust engine only reads the clock under profiling and the old `dict` reported `solve_us=0` on every unprofiled solver.
Index-status: proposed
Date: 2026-09-16

## Context

Items 6, 7 and 9 of
[the 2026-09-16 improvement list](../../plan/improvement-list-2026-09-16.md).
Two consumers, one shape:

- **Glaurung** (July, `docs/history/axeyum-integration-2026-07/` in the
  Glaurung tree): of `vwififlt`'s both-sat queries, **781 of 989 (79 %)**
  returned different valid models between z3 and Axeyum, and the
  finding-set differences between the two backends (z3 55/19, Axeyum 91/36)
  were traced entirely to `concretize_addr` binding `addr == any-satisfying-model`.
  Verdicts never disagreed (0 of 18,508). Glaurung's own fix was a
  `glaurung-min-unsigned-v1` policy on ITS side ([ADR-0236], [ADR-0238]),
  paid in extra solves per concretization.
- **The cindergraph defects example** (`python/examples/cindergraph_defects/check.py`):
  `solve()` re-runs `axeyum_cli` under `bounded(query, b)` for
  `b ∈ (1, 16, 256, 4096)` after every `sat`, so a witness a reader can
  check by hand costs up to five subprocess solves per finding.

The sizing note
([2026-09-16-model-preference-sizing.md](../11-design-review/2026-09-16-model-preference-sizing.md))
read the SAT core before any code was written, and its first finding changes
the design: **the pure Boolean core already decides `false` first.**
`Cdcl.initial_phase` defaults to `false` (`proof_sat.rs:2446`), the shipped
`PhasePolicy::pinned()` never rephases, and every `phase[var]` starts `false`.
What puts a `1` on a free symbol bit in a returned model is **phase saving**
(`proof_sat.rs:3158`): a bit assigned `true` inside a later-retracted branch
keeps `phase = true` and is decided `true` the next time. So "initial phase
all-false" is today's behaviour, and a preference that differs from today has
to override phase saving — which is exactly z3's `phase=always_false`
(`sat_solver.cpp:1717-1741`, `guess()` returns `false` without consulting
`m_phase`) and CaDiCaL's `forcephase`. cvc5's MiniSat has the per-variable
form (`freezePolarity`, `Solver.h:790`).

## Decision

**A `sat`'s model is chosen by a policy on `SolverConfig`, the policy ships as
`Any` — the search byte-for-byte as it was — and the two consumers' needs are
one mechanism: a replay-checked model-finishing pass on the lifted model, plus
a bounded re-solve ladder in the front door. The SAT-core forced phase the
brief asked for is wired, measured, and shipped OFF behind a lever.**

### The policy

```rust
pub enum ModelPreference { Any, PreferZero, LeastUnsigned }   // Default: Any
pub const DEFAULT_MODEL_PREFERENCE: ModelPreference = ModelPreference::Any;
SolverConfig { model_preference, .. }   // `.with_model_preference(..)`
```

| variant | search | after a `sat` |
| --- | --- | --- |
| `Any` | as shipped | nothing |
| `PreferZero` | as shipped; with `AXEYUM_MODEL_PREFERENCE_PHASE=on`, every decision is `false` (`Cdcl.forced_phase = Some(false)`) | the replay-checked shrink (`shrink_model_toward_zero`), bounded by what the solve spent |
| `LeastUnsigned` | as `PreferZero` | the magnitude ladder over every declared bit-vector constant, then the shrink inside the winning rung; the unbounded model shrunk when no rung succeeds |

A preference is a **model finishing pass** (and, with the lever, a
decision-order heuristic), never a verdict input. The finishing passes only
ever REPLACE a model with one `check_model` (front door) or the engine's own
replay (warm engine) accepted against the query's own assertions. The SAT-core
override is read at the one decision site (`proof_sat.rs`, `let polarity =
self.forced_phase.unwrap_or(self.phase[var])`) and nowhere else: propagation,
conflict analysis, the clause database, restarts and the DRAT stream are
untouched, so a verdict cannot change and every `unsat` carries the proof it
always did. The saved phases keep being recorded underneath it.

**Budget.** The shrink may spend `max(elapsed, MODEL_SHRINK_MIN_BUDGET =
100 ms)` where `elapsed` is what the solve that produced the model cost, never
past the query's deadline, and at most `MODEL_SHRINK_EVALUATIONS = 4_096`
evaluator calls (`shrink_deadline`, both constants registered). Measured
reason: with the evaluation budget alone the pass spent 25 s finishing a
1.7 s `sat` on `QF_BV/Sage2/bench_12354.smt2` (549 symbols, 192 KB). A
preference therefore at most doubles a query.

### The finding that shaped `PreferZero`: the forced phase alone moves no model

The forced phase was wired first and measured on its own. It is observable —
on `(a ∨ b) ∧ (a ∨ ¬b)` the shipped search returns `b = true` (the saved phase
of the retracted `a = false` branch) and the forced search `b = false`, at the
CNF level (`axeyum-cnf` unit test) and through `SatBvBackend`
(`prefer_zero_reaches_the_one_shot_backend`). But over the committed `QF_BV`
corpora it moved **0 of 15** `sat` models, and on a hand-written shape with
three witnesses for `y` (`0xF4`, `0xF5`, `0xF6`) it returned the same `0xF5`
as `Any`. The reason is structural, not a plumbing fault: the variables the
search decides are Tseitin GATE variables far more often than symbol input
bits, and a gate decided `false` propagates a `1` into an input through any
negated AIG edge (`v ↔ (¬a ∧ b)` false with `b` known true forces `a = 1`).
The polarity a bit-blasted model shows on its INPUTS is not the polarity the
core decided. z3's `phase=always_false` has the same property on its
bit-blaster; the option is a search heuristic, not a model guarantee.

So `PreferZero` finishes where the inputs are visible: `shrink_model_toward_zero`
walks the declared `Bool`/bit-vector constants in declaration order, bits
from the most significant down, clears each set bit and keeps the candidate
iff the replay accepts it — deterministic, budgeted as above, a local minimum
in the unsigned order and never claimed as the global one. With it, the
hand-written shape returns `y = 0xF4` and the corpus identity test has a
fixture it can fail on. Inside `LeastUnsigned` the shrink replays against the
rung's EXTENDED stack, so it cannot push a witness past the magnitude the rung
promised: `len = -1` stays `-1` rather than becoming the unsigned-smaller
`INT_MIN`. The warm engine (`IncrementalBvSolver`) runs the same pass after
its own replay, against every active assertion plus the assumptions, so
Glaurung's `check_assuming` gets the finished model too.

**And the forced phase costs search time without buying a model**, which is
why it ships off (`DEFAULT_MODEL_PREFERENCE_PHASE = false`). The A/B below
ran it both ways: phase on, +27 % wall on the both-decided files, one stable
gain and one stable loss (the loss is the SEARCH — probed at a 90 s budget,
`sat` in 24.9 s against 1.2 s); phase off, the shrink alone, +12 %, no
movers. `AXEYUM_MODEL_PREFERENCE_PHASE=on` re-arms it per process so the
number can be re-taken; the plumbing stays, tested through that lever.

### Where it reaches

- **The shrink**: the text front door (`solve_smtlib_with_model`, so
  `solve_smtlib`, the session's `check-sat`/`check-sat-assuming`, and the
  Python `smt.solve`) and the warm engine (`IncrementalBvSolver`, after its
  own replay, so `check`/`check_assuming` and the Python `Incremental`).
  `SatBvBackend::check` on its own does not finish models: it is the search,
  and the front door and the warm engine are the two places a consumer gets a
  model from.
- **The forced phase (lever on)**, one-shot: `SatBvBackend` →
  `primary_sat_search(config, …)` →
  `solve_with_native_cdcl(…, config.model_preference.forced_phase())` →
  `axeyum_cnf::solve_with_drat_proof_with_limits_and_phase`. The old
  `solve_with_drat_proof_with_limits` now calls the new one with `None`.
- **The forced phase (lever on)**, warm: `IncrementalBvSolver::with_config`
  (and `with_config_and_profiling`) → `IncrementalCnf::set_forced_phase` →
  `IncrementalSat::set_forced_phase` → `NativeIncrementalCdcl::set_forced_phase`.
  `warm_config_is_honored` now names `model_preference` as read by both
  routes.
- **Front door**: `(set-option :model-preference any|zero|least-unsigned)`
  joins the closed honoured set of [ADR-0541] (six options now); a value
  outside the three is an `error` naming the option, not `unsupported`,
  because the option IS honoured and the value is wrong — the `:timeout
  expects milliseconds` shape. `solve_smtlib_with_model` honours
  `config.model_preference` the same way, so `solve_smtlib`, the session and
  the Python `smt.solve` all agree.
- **Process levers**: `AXEYUM_MODEL_PREFERENCE` (`any` | `zero` |
  `least-unsigned`), read once into a `OnceLock` by `SolverConfig::default()`,
  and `AXEYUM_MODEL_PREFERENCE_PHASE` (`on` | `off`), read once by
  `ModelPreference::forced_phase`; unset is the shipped value, a malformed
  value panics naming the variable (the `config_lever` contract: a typo must
  not measure the shipped arm and report it as the other). Both registered in
  `config_registry.rs` (`DEFAULT_MODEL_PREFERENCE`,
  `DEFAULT_MODEL_PREFERENCE_PHASE`).
- **Python**: `smt.solve(…, model_preference=)`, `solver.Config(model_preference=)`,
  `Incremental.model_preference`.

### The ladder (item 7)

```rust
pub const LEAST_WITNESS_BOUNDS: [u128; 4] = [1, 16, 256, 4096];
pub struct LeastWitness { pub solved: SmtLibSolved, pub bound: Option<u128> }
pub fn solve_smtlib_least_witness(input: &str, symbols: &[&str], config: &SolverConfig)
    -> Result<LeastWitness, SolverError>
```

Decide the script; on a `sat`, for each bound `b` assert `x ∈ [-b, b]` in
two's complement (`bvsle x b ∧ bvsge x (bvneg b)`) for every named symbol —
every declared bit-vector constant of width ≤ 128 that is not a packed
`String` when `symbols` is empty — skipping a symbol whose width the rung no
longer bounds (`b ≥ 2^(w-1)`); solve the extended stack; the first `sat` rung's
model replaces the search's and `bound` reports it; a rung's `unsat`,
`unknown` or error moves to the next; no rung succeeding returns the unbounded
model with `bound: None`. The rungs share `config.timeout` with the unbounded
solve. **The verdict is always the unbounded one**; a rung can only replace the
MODEL of a query already decided `sat`, and a rung's model satisfies the
original assertions by construction (a superset) — re-checked with
`check_model` before it is accepted, a rung that fails that check is treated
as `unsat`.

**Why magnitude and not unsigned order.** The witnesses a defect reader wants
are the wrap cases: `a = 0xFFFFFFFF, b = 1` for `a + b < a`, `len = -1` for a
`len > 256` check that passes signed and is bypassed unsigned. Those are
magnitude 1 and unreachable under an unsigned bound of any size below the
width. The name `LeastUnsigned` is the ordering the policy approximates
(Glaurung's term); the bound it uses is stated here so nobody reads
`least-unsigned` as `bvule`.

Exposed as `(set-option :model-preference least-unsigned)` (the session runs
the ladder over every declared bit-vector constant after each `check-sat`, so
`get-model`/`get-value` answer with the witness) and as
`axeyum.smt.least_witness(script, symbols=[], …) -> Witness` (`.outcome`,
`.status`, `.bound`).

### Typed stats in Python (item 9)

`solver.Incremental(arena, config=None, *, profile=False)` and
`Incremental.stats() -> IncrementalStats` with `word_rewrite_ns`,
`bit_blast_ns`, `cnf_encode_ns`, `solve_ns`, `model_lift_ns`, `replay_ns`,
`total_seconds`, `root_encodings`, `checks`, `aig_nodes`, `cnf_variables`,
`cnf_clauses`, `delta_since(earlier)`, `as_dict()` (the old shape), and
**`profiled`**. The last field is the finding: `IncrementalBvSolver` reads the
clock only under `with_config_and_profiling`, the Python wrapper only ever
called `with_config`, so the old `dict` reported `solve_us=0` and `checks=0`
on every solver a Python consumer could build. That is why Glaurung wrote its
own `check_assuming_measured`. A consumer can now ask for the timers and can
see whether the zeros it reads are measurements.

## Evidence

### Identity, non-vacuity, determinism, replay (`tests/model_preference_2140.rs`)

The population is derived from `corpus/regression/{qf_bv,cvc5/qf_bv}` and
`corpus/micro` — every flat `(set-logic QF_BV)` script, 53 files, of which
10 parse-skip (front-end gaps) and 9 are `sat` — never from a list.
`corpus/qfbv-curated` is deliberately excluded (seven of its files are
`unknown` at 5 s and would make this a budget test). Three fixtures were
added to `corpus/regression/qf_bv/` for this ADR because the committed `sat`
fixtures all had unique or already-zero models, so no preference could be
visible on them: `sat_free_bits_model_choice.smt2` (three witnesses for
`y`), `sat_wrap_add_witness.smt2` (`a + b < a`) and
`sat_signed_check_bypass.smt2` (`len ≤ₛ 256 ∧ len >ᵤ 256`). They are ordinary
`:status sat` seeds and the soundness sweep walks them like any other.

| claim | test | count |
| --- | --- | --- |
| `Any` is the shipped default and returns the same verdict and model as `SolverConfig::default()` on every fixture | `any_is_the_shipped_search_on_every_qf_bv_fixture` | 43 compared, 9 `sat` |
| that identity CAN fail: `PreferZero` moves at least one model, verdicts never move, every `sat` replays | `the_identity_is_not_vacuous_and_prefer_zero_only_moves_models` | 1 of 9 models moved |
| same input, same policy, same model, twice, under all three policies | `same_input_same_policy_same_model` | 129 pairs |
| `LeastUnsigned` never moves a verdict; every returned model replays against the ORIGINAL assertions | `least_unsigned_never_moves_a_verdict_and_every_model_replays` | 9 `sat`, 9 replayed |
| the forced phase reaches the one-shot backend when the lever is on (`b` false under `PreferZero`, true under `Any`; child process) | `the_forced_phase_reaches_the_one_shot_backend_when_on` | — |
| the warm engine finishes its model (`y = 0xF4` under `PreferZero` and `LeastUnsigned`, `check_assuming` replays) | `prefer_zero_reaches_the_warm_engine` | — |
| both levers are read and a malformed value of either refuses | `the_env_lever_is_read_and_a_malformed_value_is_refused` (child processes) | — |
| `a + b < a` → bound 1, `(a, b) ∈ {(-1, 1), (1, -1)}` | `least_witness_finds_the_magnitude_one_wrap` | — |
| `len ≤ₛ 256 ∧ len >ᵤ 256` → bound 1, `len = 0xFFFFFFFF` | `least_witness_finds_the_negative_length` | — |
| `x = 100000` → `bound: None`, the unbounded model | `least_witness_falls_back_to_the_unbounded_model` | — |
| the lever is read, and `AXEYUM_MODEL_PREFERENCE=sideways` refuses | `the_env_lever_is_read_and_a_malformed_value_is_refused` (child process) | — |

The SAT-core half has its own unit test
(`axeyum-cnf` `forced_false_phase_overrides_the_saved_phase_and_none_is_the_plain_search`):
on `(a ∨ b) ∧ (a ∨ ¬b)` the shipped search returns `[true, true]` — `b` at
its SAVED phase from the retracted `a = false` branch — and the forced search
returns `[true, false]`, with the `None` arm equal to the plain entry point.
The prediction was written before the test ran and held.

### Mutation controls (`scripts/tests/mutation_controls.py model-preference-2140`)

| mutation | killed (measured 2026-09-17) |
| --- | --- |
| `DEFAULT_MODEL_PREFERENCE = PreferZero` | exactly 1: `any_is_the_shipped_search_on_every_qf_bv_fixture` |
| the decision site reads `self.phase[var]` (override inert) | exactly 1: `the_forced_phase_reaches_the_one_shot_backend_when_on` |

The second row is the finding again from the other side: with the SAT-core
override inert, the corpus non-vacuity test still passes, because the shrink
moves the three-witness fixture on its own. The one test that dies is the one
that looks at the core directly, through the lever.

### The price of `PreferZero` on `QF_BV` (A/B)

`bench-results/parity-lists/QF_BV.txt` (200 files), s7, one binary and two
environment values per run, arm A always the variable unset, arms interleaved
per file and alternating in order, 24 s / 8 GiB, two halves of 100 files
concurrently on core pairs `1,9` and `3,11`; timing by `$EPOCHREALTIME` with
the 200 ms sleep self-check (`bench-results/model-preference-20260916/`,
`ab-env.sh`, `summarize.py`). Three runs, because the first one's answer
raised the second question:

| run | arm B | binary | decided A / B | sat/unsat A → B | wall, both-decided (ms) | B slower / A slower (>10 % + 50 ms) | movers (3× recheck) | flips | `:status` disagreements |
| --- | --- | --- | ---: | ---: | ---: | ---: | --- | ---: | ---: |
| B | `zero`, phase ON, evaluation-budgeted shrink | `b6f0c14f` | 186 / 186 | 57/129 → 56/130 | 147 933 → 188 236 (**+27 %**) | 25 / 4 | 1 STABLE-GAIN (`bruttomesso/core/ext_con_008_001_0064`: never → unsat 0.1 s), 1 STABLE-LOSS (`Sage2/bench_12354`: sat 1.3 s → never) | 0 | 0 |
| C | `zero`, phase OFF, time-budgeted shrink | `882b3137` | 186 / 186 | 57/129 → 57/129 | 148 204 → 165 717 (**+12 %**) | 13 / 1 | none | 0 | 0 |
| D | `zero`, phase ON, time-budgeted shrink | `882b3137` | 186 / 186 | 57/129 → 56/130 | 146 695 → 182 710 (**+25 %**) | 23 / 3 | the same two files as run B (gain 0.1 s, loss never), not re-rechecked | 0 | 0 |

PAR-2 (24 s): A 4106 / B 4302 (run B); A 4101 / C 4189 (run C); A 4100 /
D 4274 (run D). Exit status nonzero: 0 rows in every run. Timing-unit sanity:
0 rows failed.

Run D reproduces run B on the final binary with the shrink time-bounded, so
the +25 % and the two movers are the PHASE's: the loss was probed on s4 at a
90 s budget, `sat` in 24.9 s under the phase against 1.2 s without — the
search, not the shrink. The gain is real and stable but is one file, and the
phase moved no corpus model the shrink did not. Run C — the shrink alone — is
the shipped `PreferZero`: +12 %, no movers, and the models actually change.

**Replay.** A `sat` printed by `smtcomp_cli` has already replayed inside
`SatBvBackend` (a failed replay is `unknown`, never `sat`), so every decided
`sat` above passed replay. Independently, `replay-check.py` re-solved every
arm-B `sat` (56 files) on s4 through `axeyum.smt.solve(…,
model_preference="zero").replay()`: **52 replayed, 0 failed**, 4 undecided
within 24 s on the loaded dev box.

## Alternatives

- **An initial-phase option only.** Rejected by the sizing: the core's initial
  phase is already `false`; the option would rename today's behaviour.
- **Per-variable polarity pins (cvc5's `freezePolarity`) on symbol bits only.**
  Would not have fixed the finding above — an input bit is still set to `1`
  by propagation from a gate decision — and the CNF core has no notion of
  "symbol bit". The shrink acts on the lifted model, where the inputs are
  visible, and is search-independent.
- **Exact minimisation (`optimize::minimize_bv`, `minimize_bv_signed`).**
  Exists, one objective at a time, exponential-then-binary probing. The
  ladder is four bounded solves over ALL symbols at once, which is what a
  witness-for-a-reader wants; a consumer that needs the true minimum of one
  expression has the optimizer.
- **Making `LeastUnsigned` an unsigned bound (`bvule x b`).** Rejected: the
  defect example's own witnesses are negative, and the brief's two required
  shapes are unreachable under it.
- **Changing `Incremental.stats()`'s return type in place without `as_dict()`.**
  Rejected: `python/tests/test_solver.py` subscripted the dict, and a consumer
  that did the same would break on upgrade for no gain.

## Consequences

- `ModelPreference::Any` ships. `DEFAULT_MODEL_PREFERENCE` is registered, its
  identity test dies if it moves, and the A/B table above is what a future
  ADR would have to beat to flip it. `DEFAULT_MODEL_PREFERENCE_PHASE = false`
  is registered and dated; the SAT-core half is one lever away for anyone who
  wants to re-measure it on another division.
- `check.py` in the defects example can drop its `BOUNDS` loop for
  `axeyum.smt.least_witness` once item 1 of the list (call the library, not
  the subprocess) lands; this ADR does not touch the example.
- Glaurung's `ConcretizationPolicy` can select `zero` or `least-unsigned` per
  process (`AXEYUM_MODEL_PREFERENCE`) or per `Config`; the finding-parity
  sweep its reviewer checklist asks for is now a one-variable experiment.
- The honoured option set of [ADR-0541] is six; `axeyum_cli`'s docs and the
  session tests say so.
- `Incremental(profile=True)` is the way to get timers; the default stays
  unprofiled so a production client does not pay clock reads.

[ADR-0236]: adr-0236-canonical-tcpip-authority-policy.md
[ADR-0238]: adr-0238-extremal-model-coverage-union.md
[ADR-0541]: adr-0541-the-smt-lib-front-door-answers-commands-or-says-unsupported.md
