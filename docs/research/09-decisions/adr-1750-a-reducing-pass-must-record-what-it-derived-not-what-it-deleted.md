# ADR-1750: A reducing pass must record what it DERIVED; what it deleted is optional

Status: accepted
Date: 2026-09-07
Index-summary: The proof-producing SAT core may now run `simplify`/`vivify`/`bve` before search and still emit ONE DRAT proof of the original formula (`axeyum_cnf::inprocess`, `solve_with_drat_proof_inprocessed`). Measured obligation: of the two halves of what a pass emits, only the `Add` half is soundness-critical — making the passes silent about every clause they derived is rejected 38 of 38 times, while dropping every `Delete` leaves all 38 proofs valid, because deletion only shrinks the checker's active set and RUP is monotone in it. Also measured: a DRAT prefix does NOT certify that an added clause was entailed (`check_drat` accepts RAT, which is satisfiability-preserving), so the soundness obligation is carried end to end — 521 corrupted passes produced a wrong `unsat` and the checker rejected all 521. Pointing a second checker at the path found a real bug: `check_drat` and `check_drat_backward` disagreed, because a deletion names a literal MULTISET and all three lookups matched only the set — `(b)` and `(b ∨ b)` are set-equal, and only one of them propagates. Default stays OFF: BVE cuts propagations per conflict to a median 0.426 and raises conflicts per second 1.875x, closing essentially the whole measured 2.56x gap to Kissat, but costs 1.2-88 s against a break-even of 59k-131k conflicts (median ~92k, flat across a 100x range of instance size).
Index-status: accepted

## Context

[ADR-1721](adr-1721-a-preprocessing-step-owes-one-of-three-obligations-chosen-by-the-direction-it-can-break.md)
settled what a *term-level* preprocessing step owes, and its rule is chosen by
what the step does to the model set. This ADR is the same question one layer
down, at the CNF, and it arrives with a measurement attached rather than as a
generalisation of that one.

The [2026-09-07 boolean-core lane][bench] decomposed
`conflicts/s = propagations/s ÷ propagations/conflict` against Kissat 4.0.4 over
eight `p4dfa` instances on one idle host. Our propagation *rate* is within ~1.4x;
our *propagations per conflict* is a median **2.56x worse**, up to 7.72x. It
pre-registered and refuted the alternatives — restarting 8.4x more often makes
the ratio worse, `analyze`'s per-conflict mark array is worth 1.6% — and left
exactly one candidate, explicitly as *not run*: `solve_with_drat_proof` runs none
of this crate's own `vivify`, `simplify` or `bve`, while Kissat's `probe`
umbrella shrinks the formula its propagation runs over.

[bench]: ../12-performance/bench-boolean-core-2026-09-07.md

Three things were measured before any code was written, and the first corrects
the framing this work was started under:

1. **The passes are wired, at the solver level, and off by default.**
   `axeyum_solver::sat_bv_backend::inprocess` runs `simplify_within` → optional
   `vivify_within` → `eliminate_variables_within` → `compact`
   (`sat_bv_backend.rs:1238-1244`). `SolverConfig::cnf_inprocessing` defaults
   `false` (`backend.rs:375`). So "we have the code and never call it" is true of
   `proof_sat.rs` and false of the workspace.
2. **The certificate does not survive that path.** With inprocessing on, the
   `unsat` proof is checked against `solve_formula` — the *reduced* formula
   (`sat_bv_backend.rs:297`). No pass's DRAT enters the emitted stream. Of the
   three passes only `vivify` produced a `Vec<DratStep>` at all; `simplify`'s
   module doc said so in its own words ("does not yet emit DRAT deletion steps")
   and `bve` emitted nothing.
3. **The 2.56x figure is against a completely unreduced formula**, because the
   boolean-core measurements ran through `boolean_core_profile` →
   `solve_with_drat_proof_counted` on raw DIMACS, a path with no preprocessing.

Point 2 is the one that decides an ADR rather than a patch: a solver that
preprocesses and then emits a proof of the preprocessed formula has narrowed what
its certificate certifies, and nothing in the pipeline announces it.

## Decision

**1. Inprocessing on the proof-producing path emits its derivation into the same
stream as the search, so the concatenation is a proof of the formula the caller
handed in.** `axeyum_cnf::inprocess::inprocess_into` runs the enabled passes and
streams their steps to the caller's `DratSink` before the search writes a byte;
`solve_with_drat_proof_inprocessed` and
`solve_with_drat_proof_counted_inprocessed` are the entry points.
`InprocessOptions::OFF` is the default everywhere and is bit-for-bit the prior
behaviour — no existing caller's trajectory, verdict or DRAT bytes move.

**2. Every step every pass emits is plain `RUP`.** No `RAT` step, no extension
variable, for all three passes — including BVE, which is only *equisatisfiable*:
its resolvents are ordinary resolution and the model direction is carried by
`Reconstruction`, which a DRAT proof is not asked to express. So the prefix
verifies under any RUP-only checker and does not depend on a pivot-literal
convention.

**3. Order is a property of the emission site, not of a post-hoc sort.** Each
`Add` is emitted while the clauses that justify it are still present, and only
then are they deleted. The recorder is threaded *through* each pass's fixpoint
loop rather than reconstructed by diffing input against output, because
`simplify`'s round-`n` strengthening can use as its witness a clause round `n-1`
strengthened: a diff has **no** ordering guaranteed to verify, and would produce
an unverifiable proof for a correct transformation.

**4. The obligation is on what a pass DERIVED, not on what it deleted.** Measured
over a 19-instance corpus × 5 pass combinations:

| corruption of the emitted prefix | proofs built | rejected |
|---|---:|---:|
| the passes stay silent about every clause they derived (drop all `Add`s) | 38 | **38 (100%)** |
| the passes emit no deletions at all (drop all `Delete`s) | 38 | **0 — every proof still valid** |

Deletion only shrinks the checker's active set and `RUP` is monotone in it, so
omitting deletions leaves a strict superset of the formula the search ran over.
**A pass that reduces purely by deleting — subsumption with no strengthening — is
therefore sound to run silently; it costs checking time, not correctness.** Both
directions are asserted in `tests/inprocess_proof_path.rs`, so the asymmetry is a
checked property and not a remark. It also decides where the cost is: on the
3.1M-variable `p4dfa` instance BVE's prefix is 37.7 M steps and subsumption's is
92 k, three orders of magnitude apart for the same reason.

**5. A deletion names a literal MULTISET, not a literal set.** All three
deletion lookups — `position_of` (`drat.rs`), `RecordSlot::pop_matching`
(`drat_backward.rs`) and `find_active_id` (`lrat.rs`) — now prefer the live
clause whose literal multiset the deletion names, falling back to any set match.
This is forced by decision 3: the normalization prelude puts `(b)` and `(b ∨ b)`
live in the active set at the same moment on purpose, they are set-equal and
multiset-different, and a checker's unit propagation counts literal
*occurrences* — so `(b)` is a unit to it and `(b ∨ b)` is not, and **which copy
a deletion removes decides whether later steps can propagate**. See
"A checker bug the inprocessed proof found" below.

**6. The default stays `OFF`, and the number a scheduling decision needs is the
break-even, not the wall time at one budget.** See Consequences.

## A checker bug the inprocessed proof found

`check_drat` and `check_drat_backward` **disagreed** on a real inprocessed
proof — forward `Ok(true)`, backward `Err(StepNotVerified { step: 41 })` — the
first time a second checker was pointed at this path. The cause is a comment in
`drat_backward.rs` asserting the opposite of decision 5: *"which of several
identical live clauses is removed is immaterial — they have the same literal
set"*. True for every clause without a repeated literal; false for the pair this
pipeline manufactures deliberately. `check_drat` scans insertion order and
removed the original (right, but by luck of scan direction); the backward checker
takes the most recent match and removed the deduped clause, leaving one that
cannot propagate, and rejected a valid proof.

The bug direction is **rejection of valid proofs**, never unsound acceptance, and
the fix is a completeness fix: both candidates are logically the same clause, and
the one now kept is the one that propagates more, so nothing rejected for a good
reason becomes accepted. It matters because the backward route is the usable one
at scale (231x faster than forward here) and because `find_active_id` sits on the
path to Lean/Alethe — a certificate that verifies but cannot elaborate stops at
the crate boundary.

Mutation control on a scratch copy, one revert at a time: reverting the backward
half kills exactly one test, reverting the forward half kills exactly the same
one, and the unmutated control passes 86.

## What a DRAT prefix does not carry, and how the negative test had to change

The pre-registered soundness-negative test was "drop one literal from a clause a
pass added — the pass strengthened further than it was entitled to — and require
the checker to reject". **It is false, and the first run said so**: 11 of 12
over-strengthened BVE mutants on `pigeonhole-3-2` were accepted. Two independent
reasons, and only the first was foreseeable:

1. On an unsatisfiable formula the prefix can drive the active set to
   inconsistency — BVE refutes small pigeonhole outright — after which *every*
   clause is `RUP` and a shorter one is a valid step.
2. Restricting to **satisfiable** formulas, where 1 cannot happen, 6 of 25 were
   still accepted. `check_drat` accepts `RUP` **or `RAT`**, and `RAT` is
   *satisfiability-preserving*, not entailment-preserving. **A DRAT proof does
   not certify that each added clause was entailed** — only that adding it
   preserved satisfiability, which is exactly what an `unsat` proof needs and
   strictly less than "the pass was entitled to strengthen here".

That is an inverted negative control in the sense the contributor guide names:
the "false" case was true. It was replaced, not weakened. The soundness
obligation is now asked end to end, in the direction the format answers:
over-strengthen a clause in the reduced formula **and** in the emitted prefix (as
a buggy pass would do both), search the corrupted formula, and require that
whenever this turns a satisfiable original into an `unsat`, the concatenated
proof is rejected. **521 corruptions produced a wrong `unsat`; the checker
rejected all 521**, floor-asserted so a run in which none did would fail rather
than pass while checking nothing.

The step-level mutation is kept as a measurement (1,287 of 2,320 rejected) with a
floor rather than an equality, because pinning it would pin a number the format
does not owe us.

## Consequences

**The propagation-volume hypothesis is confirmed, and was under-predicted.** On
s5 idle, `taskset -c 0-7`, one binary (sha256 pinned), 20,000-conflict budget,
arms interleaved, 64 cells, 0 failures, counters bit-identical across repeats,
worst wall-time spread 1.025x. Over the six instances where every arm exhausts
the budget:

| median vs `off` | `subsume` | `bve` | `preprocess` |
|---|---:|---:|---:|
| propagations / conflict | 0.933 | **0.426** | **0.388** |
| conflicts / second | 1.051 | **1.875** | 1.958 |
| propagations / second | 0.990 | 0.864 | 0.874 |

`2.56 × 0.426 = 1.09`: on this metric one-shot BVE closes essentially the whole
measured gap to Kissat. Subsumption alone moves the median 7% and is *worse* on
three of eight files — the effect is entirely BVE, the only pass that removes
variables.

**A mechanism the numbers volunteered.** The reduced formula has 24-28% fewer
clauses but **17-21% more literal occurrences**, uniformly: resolvents are longer
than the clauses they replace. So propagations/second falls 13% — a change aimed
at propagation *volume* moved propagation *rate* in the opposite direction, and
the product still nearly doubles.

**The cost, stated as a break-even rather than as a wall time.** At a
20,000-conflict budget BVE loses on total time on every file (1.2-88 s of pass
against a 0.35-35 s search), which is a fact about the budget. The break-even —
`cost / (1/c_off − 1/c_bve)` — is **59k-131k conflicts, median ~92k, on every one
of the eight files across a 100x range of instance size**. In seconds of
unreduced search that is 4.6 s on the smallest and 177 s on the largest. Decided
counts at the budget: `off` 1 of 8, `subsume` 1, `bve` 1, `preprocess` 2.

That is why the default stays `OFF`. Turning it on is a scheduling decision that
should be made against the break-even table and a real solve budget, and this
sweep ran at a budget ~4.6x below break-even.

**The certificate gets much larger, and the streaming sink stops being
optional.** The search emits ~36,000 steps at this budget regardless of instance
size; BVE's prefix is proportional to the *formula*, reaching 37.7 M steps —
1,034x the search's proof — on the 3.1M-variable instance. An in-RAM
`VecProofSink` is not viable there; ADR-0381's streaming sink is the only route.
Checking still works and still points the same way: on a refutable
near-threshold random 3-SAT instance, `check_drat_backward` is **231x** faster
than forward `check_drat` (0.87 s vs 200.85 s over 203,528 steps), well past the
26x the boolean-core lane measured on its small fixture.

**Open, and named rather than implied.**

- *In-search* inprocessing is not run and not ruled out. It needs `Cdcl` to
  rebuild its arena, headers and watch lists at level zero while preserving VSIDS
  activity and saved phases. The ~92k-conflict break-even is what makes it
  interesting: a schedule re-reducing every ~100k conflicts pays roughly what one
  pre-pass pays, over a formula that keeps shrinking.
- `sat_bv_backend` still checks its `unsat` against the reduced formula, so with
  `cnf_inprocessing` on the BVE link is trusted rather than checked. Not unsound
  — the chain holds by equisatisfiability — but the checkable artifact covers one
  link, which is exactly the shape ADR-1721 names. The machinery now exists; the
  obstacle is that the backend also `compact()`s, which renumbers variables and
  breaks the correspondence between prefix and searched formula.
- Of the 113 files in the local `p4dfa` slice, 53 are ≤25 MB and were censused
  at a 20,000-conflict budget: 3 `sat`, 50 budget-exhausted, **0 `unsat`, 0
  timeouts**. So there is no `p4dfa` refutation to check at that corpus's scale,
  and the corpus-scale proof check ran on a near-threshold random 3-SAT instead.
  The 60 files above the size cut were not examined.
