# ADR-1762: the configuration surface is enumerable, recordable and dated, and a justification carries the things it rests on

Status: accepted
Index-summary: 113 governing values across dispatch, the theory engines and the Boolean layer are registered with name, module, exact literal, UNIT, what they protect, what the code does when they are crossed, whether the caller is told, and where the justification lives with its date. **24 of the 113 carry a datable justification; 89 do not.** The registry is a description, never a source — nothing in it is read by the code it describes, so registering a bound cannot change it. Four checks make it falsifiable (an entry naming a dead constant; a constant in a governed file with neither an entry nor an exemption; an unsorted or duplicated table; an entry lost to a merge), and deleting one entry kills exactly one of them. The staleness contract is the point: a dated justification must name what it `rests_on`, and `scripts/check-config-registry-staleness.py` asks git whether any of those changed after the measurement — dating `MAX_ONLINE_LRA_ATOMS` 2026-08-03, its real original date, reproduces the thirteen-month failure in one command. A run emits its configuration under the existing `--trace` flag with no new CLI surface, and the digest moves when an environment override is in force. Three defects in the checker itself were found by its own positive control, not by review, including one that made it structurally unable to fire while printing exactly what a working one prints. This ADR REGISTERS; it retunes nothing.
Index-status: accepted
Date: 2026-09-07

## Context

The solver's behaviour is governed by dozens of caps, bounds, budgets and
thresholds held as private `const`s. Nothing enumerated them, nothing recorded
which values a run used, and their justifications went stale silently. Four
measured instances, all from 2026-09-05 to 2026-09-07:

- **`MAX_ONLINE_LRA_ATOMS = 1_024`.** Its recorded justification was a
  2026-08-03 measurement (`e62086742`) that raising it made
  `QF_LRA/sc/sc-39.base.cvc.smt2` abort at 8 GiB, naming `AtomBuilder`
  normalization as the cost. `MAX_LRA_CACHED_COEFFICIENTS`, the bound that caps
  exactly that cost, landed 2026-08-06 (`96ff85930`) — **three days later**. The
  number rested on a tree in which the thing it protected against was unbounded,
  and it was never re-taken. Thirteen months. Replaced by
  [ADR-1752](adr-1752-the-lra-admission-cap-becomes-budget-relative.md).
- **The QF_NRA cross-product bound of `2`** metered in cross-products while the
  engine consuming its output meters in **atoms** and refuses above 1,024 — 15x
  apart, in incommensurable units, with no constant conversion between them (the
  measured atoms-per-cross-product ratio spans 13.1 to 30.3 across four census
  files, so any single factor is wrong by up to 2.3x). Fixed by
  [ADR-1751](adr-1751-nra-admission-is-the-consumers-capacity.md).
- **`MAX_CONGRUENCE_GROUPS = 48`** in `nia_linearize.rs` changes soundness mode
  above the cap with **no branch and no signal to the caller**: the `if` has no
  `else`. The direction had to be derived from semantics because nobody had.
- **A prior cap's rationale** said the code OOM-killed the host at 64 GiB;
  re-measured, peak memory is 3.3 GiB with zero aborts in 124 runs. The fixes
  that falsified it landed afterwards.

These are four instances of three distinct gaps — no list, no per-run record, no
date — and each gap is what made the others expensive.

## Decision

**A governing value is registered, not merely present.**
`crates/axeyum-solver/src/config_registry.rs` holds a `ConfigEntry` per value:
name, module, the exact literal, the **unit**, what it protects, what the code
does when it is crossed, whether the caller is told, what guards an unsignalled
crossing, any environment override, the justification with its date, and a note.

Three properties of that decision matter more than the table:

**1. The registry is a description, never a source.** Nothing in the module is
read by the code an entry describes. Registering a bound cannot change it, and a
wrong entry cannot change a verdict — it can only fail the module's own checks.
This is what makes it safe to register 113 values in one change.

**2. A unit is a required field.** The QF_NRA/QF_LRA mismatch was invisible
because neither file's text mentioned the other's unit. A registry in which
`unit` is optional would have recorded both bounds and still hidden the defect.

**3. A dated justification must name what it `rests_on`.** A date with no
dependencies can never go stale, so it would be a date that means nothing. This
is enforced by a test, and it is the whole staleness contract:
`MAX_ONLINE_LRA_ATOMS`'s entry names `MAX_LRA_CACHED_COEFFICIENTS` — the
dependency whose absence let a measurement stand for thirteen months after the
commit that falsified it.

**Coverage is claimed per FILE, not globally.** `GOVERNED_FILES` lists the 19
files the registry covers completely; a constant in one of them must be
registered or named in `EXEMPT` with a reason. A global claim would be red the
moment any crate grew a constant, and a check that is always red is a check
nobody reads. A file absent from the list is not claimed, which is a gap this
module states rather than hides.

**Recording is opt-in, off by default, and adds no CLI surface.**
`ConfigTraceGuard` is the fifth guard on the existing `--trace` /
`AXEYUM_TRACE=1` flag, alongside `TheoryLayerStatsGuard`, `BvLayerStatsGuard`,
`DlOnlineStatsGuard` and `FrontDoorStatsGuard`. Off costs one thread-local
`Cell<bool>` read.

**This decision registers. It does not retune.** No constant's value changes.
Three lanes this week found that changing one without establishing what it
protects produces a plausible change that makes things worse, and one found that
every raised value bought the same two files while cost grew monotonically. A
value that looks wrong is recorded with evidence and left alone.

## What the registry says about the tree, measured

| | |
| --- | --- |
| Entries | 113 |
| **Dated justifications** | **24 (21%)** |
| Undated | 89 (79%) |
| Genuinely stale | 0 |
| Crossing **with no branch and no signal** (`Signal::None`) | **35** |
| Crossing reported to the caller (`Signal::ToCaller`) | 51 |
| Crossing is the normal regime (`Signal::NotApplicable`) | 27 |
| Governed files | 19 |
| Constants classified as non-governing (`EXEMPT`) | 12 |
| Environment overrides | 2 (`AXEYUM_MEMORY_LIMIT_MB`, `AXEYUM_NRA_ADMISSION`) |

**35 of 113 bounds change behaviour with nothing telling the caller.** Each names
a `guarded_by` — a test requires it — and in every case the guard is model
replay, a valid-lemma argument, or the fact that the pass only adds constraints.
That is a real answer rather than an absent one, which is the difference this
registry makes: before it, the question had no field to be answered in.

The undated 79% is the headline, and it is deliberately reported in the run's
own `--trace` line (`dated=24`) so a registry that grew undated entries
indefinitely could not do so unnoticed.

**The best-justified entry in the tree is
`memory_budget::ENCODING_BYTES_PER_CLAUSE`**, and it is the model for the rest:
its doc carries a table of measured peaks over `bvmul` commutativity miters,
names the host, gives the date (2026-08-21), **and ships a re-measurement test**
(`crates/axeyum-solver/tests/memory_budget.rs`) so the number can be re-taken
rather than re-argued.

## Findings recorded, not fixed

Each of these is registered with evidence and left in place, per the scope rule.

- **Two constants named `MAX_CONGRUENCE_GROUPS`, both `48`, with opposite
  signalling contracts.** `axeyum_rewrite::int_divmod`'s reports its crossing as
  `ZeroDivisorCongruence::Omitted` and `auto::guard_zero_divisor_sat` branches on
  it (ADR-1730). `axeyum_solver::nia_linearize`'s signals nothing at all.
  Nothing links them. The `nia_linearize` one is a **completeness** cost and not
  a soundness hole, because `check_with_nia` accepts a `sat` only after
  `replay_sat` re-evaluates the ORIGINAL assertions under the ground evaluator,
  which a model violating `div`/`mod` functionality cannot pass — a fact derived
  from the code, since neither doc comment states it.
- **`MAX_CERTIFIABLE_BOOLS = 22` exists twice**, in `dpll_lia.rs` and
  `dpll_t.rs`. In one it switches the verification method; in the other it
  declines the certificate outright. Same name, same value, different contract.
- **`auto::INT_REAL_RELAX_BUDGET_SHARE`.** When the intended one-sixth share
  underflows to zero the code returns the caller's config **unchanged** — the
  full, unshrunk timeout — rather than skipping the refuter or clamping to a
  floor. The sharing policy is bypassed silently at exactly the small-budget end
  where starvation matters most.
- **`dl_online::MAX_DL_ATOMS`.** `atom()` returns `None` on size, which at the
  call site is indistinguishable from "this term is not difference-shaped". A
  size refusal and a structural decline share one signal, so no trace can
  attribute the route change to the bound. The same class as the unit mismatch:
  a gate whose meaning is lost at the boundary.
- **`dpll_lia::MAX_BELLMAN_FORD_DIFF_EDGES = 256` is tighter than
  `MAX_TWO_EDGE_DIFF_EDGES = 512`**, the cheap pre-check that feeds it, so the
  cheap check admits inputs twice as large as the thorough fallback behind it.
  Neither is measured and the relationship is undocumented.
- **`auto::MAX_BOUND_PROP_ROUNDS`** reaching its cap without a fixpoint hands
  the caller partial bounds with no indication the fixpoint was not reached.
- **Four independent copies of the same CDCL heuristics** (`REDUCE_FIRST`,
  `GLUE_LBD`, `VSIDS_DECAY`, `LUBY_UNIT`) across `lra_online.rs`, `cdclt.rs` and
  two cores in `axeyum-cnf`, none linked, one spelled `REDUCE_INC` in one place
  and `REDUCE_INCREMENT` in another.

## Consequences

**A registry that cannot be wrong is worthless**, so each failure mode has a
check that dies on it, and the deletion was performed rather than argued:
removing `simplex::MAX_PIVOTS`'s entry killed **exactly one** test,
`every_governing_constant_is_registered` (10 passed, 1 failed).

The other three: `every_entry_names_a_live_constant` (an entry naming a
constant that no longer exists, or a value the source disagrees with),
`registry_is_sorted_and_unique`, and `registry_len_matches_its_own_source` (an
entry lost to a merge). Plus two invariants the registry imposes on itself: a
`Signal::None` entry must name its guard, and a dated justification must rest on
something.

**Populations come from the source, not from a transcribed list.** Two
independent scanners read the same files —
`scripts/config_registry_scan.py` and the test's own — because a registry whose
facts were typed by hand records the maintainer's memory rather than the tree.
That paid immediately: written line-at-a-time the Rust scanner read an empty
value for a constant whose initializer sits on the next line, and blamed a
registry row that was correct.

**The staleness checker's own positive control found three defects in it that
review did not**, and two of them made it structurally unable to fire while
printing exactly what a working one prints:

- `FIELD_RE` used `^`/`$` on a multi-line blob without `re.MULTILINE`, so the
  parser returned zero entries. Caught by its own self-check, which compares
  parsed entries against the raw `ConfigEntry` literal count.
- `SYM_RE` ended in `\s*\)` while rustfmt breaks `sym(...)` across lines **and**
  adds a trailing comma. Every dated entry parsed with an empty `rests_on`, so
  the check reported "no dated justification is stale" for all 24.
- It flagged a constant's own introducing commit. ADR-0360 is dated 2026-07-22
  and `5b4c5b404` introduced all three `MAX_MBQI_FREE_INT_*` constants on
  2026-07-23; the check called those stale on its first honest run. They are not
  — recording a decision and then landing the code is the healthy order. The
  exclusion is deliberately narrow, self-dependency only, because `96ff85930`
  **introduced** `MAX_LRA_CACHED_COEFFICIENTS` and that introduction is exactly
  what falsified the 2026-08-03 measurement. Excluding introductions in general
  would have blinded the checker to its own founding example.

**Two self-reference bugs**, both producing confident, plausible, wrong failure
messages about the table: `registry_len_matches_its_own_source` counted its own
needle (114 against 113), and `consulted_keys_are_registered` matched the
`note_consulted(` call quoted in its own scanner.

**No verdict moves, measured.** 155 files across `corpus/micro` and
`corpus/regression`, recording off and on under an identical 8 s budget: zero
verdict differences. That A/B also showed the consulted set is not exercised by
it — none of the 155 printed a `consulted=` field, because those queries are
decided before reaching an instrumented gate — so
`an_instrumented_gate_records_through_the_real_path` drives a real
`simplex::Incremental::new` under the guard instead. An instrument nothing has
been shown to reach is indistinguishable from one that does not work.

**Determinism.** The emitted order comes from a sorted static and a `BTreeSet`,
never a `HashMap` or `HashSet`, because output whose order depends on
per-process hash seeding would break this tree's determinism promise.

**The staleness check is not wired into an aggregate gate here.** It is runnable
and currently green; gating decisions belong with the lanes that own those
gates.

## What this does not do

- It does not cover every crate. Nineteen files are claimed; `axeyum-cnf`'s two
  CDCL cores, `axeyum-bv`, `axeyum-aig` and most of `axeyum-search` are not, and
  their absence from `GOVERNED_FILES` is the statement of that gap.
- It does not record which values a run consulted except at four instrumented
  gates. The `--trace` line's `entries`/`dated`/`digest`/`env:` fields describe
  the configuration **in force**, which is what makes a run reproducible; the
  `consulted` field describes only the gates that have been instrumented so far.
- It cannot see a semantic dependency nobody wrote down. The staleness check is
  only as good as each entry's `rests_on`, which is why a date without one is
  rejected.
- It retunes nothing, and the seven findings above are recorded open.
