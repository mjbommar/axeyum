# ADR-2143: An opposite-polarity re-assert is a conflict, never an overwrite — `LiaTheory` and `LraTheory` lose nothing on `pop`

Status: accepted
Index-summary: The ax-proptest audit's STOP finding (ADR-2141): `LiaTheory::assert`
overwrote a live atom's polarity in place and logged only the atom INDEX, so
`pop` set the atom to `None` instead of restoring the shadowed outer value —
`push; assert(x ≥ 10); push; assert(¬(x ≥ 10)); pop; assert(x ≤ 0)` was
accepted. `LraTheory` had the same bookkeeping (its `live` list still
conflicted, but the stale marker made `rows_to_core` emit the wrong polarity, a
false lemma). Sizing: NO wrong verdict could ship — both CDCL(T) drivers
assign a SAT variable once until backtrack and map it 1:1 to an atom, and the
front door re-solves every `check-sat` from scratch; 10 committed and 67
public incremental scripts carry the script-level shape and every one agrees
with z3 before and after. Decision: a re-assert of a live atom at the opposite
polarity returns the conflict `[(a, live), (a, new)]` and touches no state, so
every log entry is a `None → Some` transition and `pop` is exact by
construction (z3's `bound_trail` stores the old value; CaDiCaL reports an
already-falsified assumption as failed — neither overwrites). Four mutation
controls, the linear-arithmetic z3 gate, and an interleaved 800-file A/B with
0 new stable losses and 0 new `:status` disagreements.
Index-status: accepted

## Context

Lane ax-proptest (ADR-2141) widened the push/pop/assert schedule fuzz in
`crates/axeyum-solver/tests/lia_online.rs` so that it reaches explicit pops
and opposite-polarity re-asserts, and the fuzz failed deterministically at
seed 9:

```text
DISAGREEMENT seed 9: theory reported no conflict but the live set is
offline-UNSAT (live=[(0, true), (1, false), (2, false), (3, true)])
```

Reduced to three steps against the theory:

```text
x >= 10 (atom 0), x <= 0 (atom 1)
push; assert(0, true)        -> Ok      (x >= 10 live)
push; assert(0, false)       -> Ok      (silent overwrite, no conflict reported)
pop
assert(1, true)              -> Ok      (x <= 0 accepted: the outer x >= 10 is gone)
```

The audit left the subject untouched and the suite red on its branch. This
lane took the subject.

### Diagnosis, at the line

`crates/axeyum-solver/src/lia_online.rs`, `impl TheorySolver for LiaTheory`:

- **Where the polarity is stored.** `assigned: Vec<Option<bool>>` (one slot
  per atom, the field at line 134) and `assigned_log: Vec<usize>` (line 138),
  the backtrack log of atom INDICES. `trail: Vec<usize>` holds, per `push`,
  the `assigned_log` length to restore.
- **Why the second assert overwrote.** `assert` (line 1788 before the fix)
  had one guard, idempotence: `if self.assigned[index] == Some(value) {
  return Ok(()) }`. Any other prior value fell through to
  `self.assigned[index] = Some(value); self.assigned_log.push(index);` — the
  slot took the new polarity and the log gained a SECOND entry for the same
  atom. `feasibility()` (line 987) then iterated the log reading `assigned`,
  so both entries said `x < 10`; the live set was feasible and the call
  returned `Ok`.
- **Why `pop` did not restore.** `pop` (line 1817 before the fix) truncated
  the log to the marker and wrote `None` into every popped slot. The popped
  entry was the inner duplicate, so the OUTER assignment's slot — which the
  log still named below the marker — was set to `None` too. A log of indices
  can only ever restore `None`; it has no record of what the overwritten
  value was.

`crates/axeyum-solver/src/lra_online.rs`, `impl TheorySolver for LraTheory`
(line 2595 before the fix): identical `assigned` / `assigned_log` / marker
shape. Here the `live: Vec<Constraint>` list is the authority for
feasibility and it ACCUMULATED both constraints, so the second assert DID
return a conflict. The damage was to the marker: after the driver's `pop`
past that conflict, `assigned[0]` was `None` while `x < 10` stayed in
`live`, and `rows_to_core` (line 2354) reads a core literal's polarity as
`self.assigned[c.atom].unwrap_or(true)` — a later conflict over that row came
back naming `(0, true)`, "x ≥ 10 ∧ x ≥ 20 is infeasible", a false lemma.

The other `TheorySolver` implementors were read: `DlTheory` (`dl_online.rs`
1781) and `EufTheory` (`euf_egraph.rs` 843) record the marker only when the
slot is `None` and let their graph / e-graph accumulate both constraints, so
the conflict is detected and the marker is never overwritten; `StringTheory`
(`string_theory.rs` 721) does the same; `UfbvTheory` (`ufbv_online.rs` 596)
records a `failure` and drives the search to `Unknown`. Only the two
arithmetic theories had the overwrite.

### The references

z3, `smt/theory_arith_core.h`: `assert_lower` / `assert_upper` push a
`bound_trail(v, old_bound, is_upper)` — the OLD value — and `restore_bounds`
walks that trail back; and `smt_context.cpp::assign_core` is only ever
reached for an unassigned literal (`m_assignment[l.index()]` is checked
first), so `theory_arith` never sees both polarities of one atom without a
backtrack between them. CaDiCaL, `assume.cpp` / `decide.cpp`: an assumption
whose literal is already false when its turn comes is reported as the
`failed` assumption and the check ends; assumptions bind per check and are
never overwritten in place.

### Sizing — could a wrong verdict ship?

Established, not assumed, in three ways:

1. **The drivers.** `cdclt.rs::assign` (line 1054) and
   `lra_online.rs::assign` (line 4418) call `theory.assert` only from a trail
   write `self.value[var] = Some(value)`, and both assign a variable only
   while it is unassigned; `theory_atom_for_var` is the identity on the atom
   range (`cdclt.rs` 582), so two variables never share an atom. The sequence
   `assert(a); assert(¬a)` without a `pop` between cannot be issued by either
   driver. `combined_theory.rs` / `combined_theory_lia.rs` assert a partition's
   base literals once each, at distinct indices.
2. **The front door.** `solve_smtlib_incremental` (`smtlib.rs` 3806)
   re-solves every `check-sat` from scratch over the active assertion set;
   script-level `push`/`pop` never drives the theory's. The minimal script
   (`corpus/incremental/13-shadowed-polarity-lia.smt2`, and the LRA twin
   `14-`) answers `unsat unsat sat` through `axeyum` at the pre-fix merge
   point, matching z3 4.13.3.
3. **The corpora.** A census (`bench-results/lia-pop-20260917/shape/
   shape_census.py`, one TSV row per file: logic, pushes, asserts, shadow
   pairs) over the 10 committed `corpus/incremental/` scripts that use `push`
   and the 3,940 public incremental scripts of QF_LIA, QF_LRA, LIA, LRA,
   QF_UFLIA, QF_UFLRA, QF_ALIA and QF_AUFLIA (97 files over 50 MB skipped by
   name, listed): 0 of the committed 10 and 67 of the public 3,940 carry the
   push / assert / assert-negation-in-a-nested-scope / pop shape (QF_LIA 6,
   LIA 5, QF_ALIA 37, QF_AUFLIA 19; none in QF_LRA, LRA, QF_UFLIA, QF_UFLRA).
   Every one of the 67 was run through the pre-fix and post-fix `axeyum`
   binaries and z3 (600 s wall per solver for the first 7, 300 s for the
   rest, 8 GiB, pinned): 31 of the 67 were answered by `axeyum` inside the budget
   (129,921 verdicts per arm; the two arms agree with each other and with z3 on
   every one); the other 36 produced NO output in either arm (rc 124 in both:
   the front door reads the whole script before answering, and these carry
   6,500–20,000 `check-sat`s each — a capability gap identical before and
   after, not a verdict). 0 disagreements. Table in
   `bench-results/lia-pop-20260917/README.md`, rows in `shape/sweep.tsv`.

So: no wrong `sat` shipped or could ship through any route in the tree. The
defect is a violation of the `TheorySolver` contract ("assertions accumulate
until the next pop; pop undoes every assertion back to the most recent
push") by two `pub` implementors, reachable by any future driver or caller
that asserts through the trait directly. It is repaired as a soundness
defect — conservative contract, soundness-negative tests, mutation controls,
oracle gates, A/B — not as a style fix.

## Decision

1. **Contract.** In `LiaTheory::assert` and `LraTheory::assert`, a re-assert
   of an atom whose OPPOSITE polarity is live at this or any enclosing level
   returns `Err([(atom, live), (atom, new)])` and touches no state. The
   conflict names the live literal and the trigger literal, which is what the
   drivers' trigger-literal precondition needs; the lemma `¬(a ∧ ¬a)` is
   valid unconditionally. Idempotent re-asserts at the live polarity stay
   `Ok`. Untracked atoms are assertions too and follow the same rule.
2. **Trail invariant.** With overwrite gone, every `assigned_log` entry is a
   `None → Some` transition, so `pop`'s restore-to-`None` is exact by
   construction. A `debug_assert!` in both `pop`s pins it (a logged atom whose
   slot is `None` would mean a lost constraint). z3's old-value trail is the
   design you need if you allow overwrite; rejecting is the smaller change
   with the same guarantee.
3. **Tests.** The red fuzz's mirror expects the conflict and counts
   `polarity_conflicts` (903 of 7,200 steps); an LRA twin of the schedule fuzz
   (its LCG now returns a finalized output — the audit's one-line fix — so
   the schedule reaches 1,656 explicit pops and 903 opposite-polarity
   re-asserts); both fuzzes check every conflict core's literals against the
   mirrored live polarity (a core naming an unasserted polarity is a false
   lemma — the LRA observable); a direct three-step unit test per theory; the
   two front-door fixtures pinned at `unsat unsat sat`.
4. **Mutation controls** (`scripts/tests/mutation_controls.py`, whole-file
   suites so a kill count is over every guard in the file):

   | suite | mutant | killed |
   | --- | --- | --- |
   | `lia-pop-conflict-check-lia` | the `Some(current)` arm reverts to the silent overwrite | 2: the three-step unit test, the schedule fuzz |
   | `lia-pop-pop-restore-lia` | `pop` stops writing `None` back | 4: + `push_assert_pop_restores_feasibility`, `non_lia_atom_declines_gracefully` |
   | `lia-pop-conflict-check-lra` | as above, in `LraTheory` | 2: the three-step unit test, the schedule fuzz (its core-polarity check) |
   | `lia-pop-pop-restore-lra` | as above, in `LraTheory` | 3: + `unit_push_assert_pop_round_trip` |

   `--check-anchors` stale=0.

## Consequences

- A driver that ever issues the sequence now gets a conflict instead of a
  silently weakened theory. Neither shipped driver issues it, so the shipped
  search is unchanged in behaviour; the A/B below is the measurement of that
  claim, not a substitute for it.
- `tests/lra_online.rs`'s LCG output is finalized, so every fuzz in that file
  now runs a different population than before (the audit's ratchet loses one
  entry: `scripts/lcg-raw-state-baseline.txt`, 56 → 55 files). All nine tests
  in the file stay green on the new population.
- `non_lia_atom_declines_gracefully` (LIA) no longer asserts both polarities
  at one level; the polarities are separated by a `pop`, and the conflict is
  pinned by exactly one test per theory.

## Gates

All counts nonzero, all from the final code state (`99f65a923` and later
docs-only commits); logs in the lane scratchpad, summary here.

| gate | result |
| --- | ---: |
| `--features full --test lia_online` | 9 passed (`polarity_conflicts=903`, `explicit_pops=1655`) |
| `--features full --test lra_online` | 9 passed (`polarity_conflicts=903`, `explicit_pops=1656`) |
| `--features z3 --test qf_lia_differential_fuzz` | 5 passed |
| `--features z3 --test qf_lra_differential_fuzz` | 6 passed |
| `--features z3 --test simplex_lra_fallback_differential` | 1 passed |
| `--features z3 --test qf_uflra_differential_fuzz` | 2 passed |
| `--features z3 --test difference_logic_differential_fuzz` | 4 passed |
| `--features full --test corpus_regression` | 2 passed (incremental corpus now 14 files) |
| `--lib --features full -- --test-threads=6` | 1,979 passed (the sweep found the two in-crate no-op probes, 1,977 + 2 fixed) |
| `run-dispatch-reason-suites.sh` | 32 suites, ALL GREEN |
| `progress_frontier --features full -- --test-threads=1` | 12 passed; no REGRESSION; `bv_reduction` 37 (baseline 30), `lia_cuts` 35 (26), `string_bound` 40 (8) PROGRESS — baselines not raised by this lane |
| mutation controls (4 suites) | killed 2 / 4 / 2 / 3, `--check-anchors` stale=0 |
| `clippy --workspace --all-targets --all-features -- -D warnings` | 268 targets examined, 0 errors (two `too_many_lines` in the fuzzes fixed by factoring helpers) |
| `cargo check --workspace --all-targets` | Finished |
| `cargo fmt --all --check` | clean |
| `check-config-registry-staleness.py` | 0 unexplained |
| `check-suite-gating.py` | PASS |
| `check-lcg-raw-state.py` | PASS, 55 files (was 56) |
| `check-merge-hygiene.sh` | PASS after `gen-adr-index.py` |
| `check-links.sh` | all links ok |

## A/B on the pinned lists

Two binaries (`smtcomp_cli`, sha256 in `bench-results/lia-pop-20260917/README.md`),
interleaved per file, order alternating, s7 core pairs `1,9` / `3,11`, 24 s
wall, 8 GiB `ulimit -v`, `$EPOCHREALTIME` with the 200 ms self-check
(read 205 ms on both shards).

| division | files | A decided | B decided | movers | `:status` disagreements A / B | non-zero exits A / B | wall A / B (s) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_LIA | 200 | 120 | 120 | 0 | 0 / 0 | 0 / 0 | 1927 / 1926 |
| QF_LRA | 200 | 107 | 107 | 0 | 0 / 0 | 0 / 0 | 2286 / 2286 |
| QF_UFLIA | 200 | 161 | 161 | 0 | 0 / 0 | 0 / 0 | 1566 / 1567 |
| QF_IDL | 200 | 111 | 112 | 1 | 0 / 0 | 0 / 0 | 2295 / 2291 |
| **all** | 800 | 499 | 500 | 1 | 0 / 0 | 0 / 0 | 8073 / 8070 |

The one raw mover (`QF_IDL/asp/WireRouting/wire.10.x.10.b.5.a.20_unsat`, A
`unknown` at 21.7 s, B `unsat` at 20.8 s) was re-run three times per arm on
one pinned core: `unsat` 6 of 6 — BOTH-DECIDE, ambient, not an effect. So:
**0 stable losses, 0 stable gains, 0 new `:status` disagreements** — the
shipped search is byte-for-byte the same behaviour, as the driver analysis
predicts.

## Alternatives rejected

- **Overwrite with an old-value trail (z3's shape).** Exact `pop`, but
  keeps the theory silently dropping a live constraint at an enclosing level
  on the overwrite step itself — `feasibility()` would report `Sat` for
  `x ≥ 10 ∧ ¬(x ≥ 10)`. The contract says assertions accumulate; a conflict
  is the honest answer and needs no new trail type.
- **Reject only for tracked atoms.** An untracked atom is still an assertion
  the caller made; `a ∧ ¬a` is a conflict whatever `a` is, and a special case
  would be one more branch to mutation-test.
- **Fix `LiaTheory` only.** The audit read `LraTheory` and found the same
  shape; the LRA unit test shows a concrete false-lemma observable (the core
  polarity), and the LRA twin fuzz would not have existed.

## Evidence

- `bench-results/proptest-box-audit-20260916/README.md` — the STOP finding.
- `bench-results/lia-pop-20260917/` — the A/B (`ab/`), the shape census and
  the 67-script sweep (`shape/`), the scripts.
- `crates/axeyum-solver/tests/lia_online.rs`,
  `crates/axeyum-solver/tests/lra_online.rs` — the fuzzes and unit tests.
- `corpus/incremental/13-shadowed-polarity-lia.smt2`, `14-shadowed-polarity-lra.smt2`.
- `docs/plan/status/ax-lia-pop.md`.
