# Inprocessing inside the proof-producing core, and what it does to the certificate

Lane `inprocessing-proof-path`, running diary. Started 2026-09-07.

Written as the work happens. Entries are appended, never rewritten: an
expectation recorded before a measurement stays visible next to its correction.

## 0. The question

The [boolean-core lane's diary](bench-boolean-core-2026-09-07.md) decomposed
`conflicts/s = propagations/s ÷ propagations/conflict` against Kissat 4.0.4 over
eight p4dfa instances on one idle host and found:

- our propagation **rate** is within ~1.4x of Kissat's — we are not slow per
  unit of work;
- our **propagations per conflict** is a median **2.56x worse**, up to 7.72x.

It pre-registered and refuted the alternatives. Restarting 8.4x more often
raises propagations/conflict by 3.9% and drops throughput 12.6%. The
per-conflict `seen` allocation — ranked first before measurement — is worth
1.6%. What it left standing, explicitly as *not run* rather than *ruled out*:

> The candidate this leaves standing is **inprocessing**: Kissat's `probe`
> umbrella … shrinks the formula before and during search, so its propagation
> cascades run over a smaller clause database. `axeyum-cnf` has `vivify`,
> `simplify` and `bve` as modules, and `solve_with_drat_proof` runs **none of
> them**.

This lane tests that, and carries the certificate through it.

## 1. Correction to the framing, before any code

The brief this lane was given says "we have the code and never call it". That is
literally true of `crates/axeyum-cnf/src/proof_sat.rs` — grep confirms zero
occurrences of `vivify`, `simplify` or `eliminate_variables` in it — but it is
not true of the workspace, and the difference matters for what is actually
missing.

`crates/axeyum-solver/src/sat_bv_backend.rs` has an `inprocess()` that runs
`simplify_within` → optional `vivify_within` → `eliminate_variables_within` →
`compact` on the Tseitin formula before handing it to the native core
(`sat_bv_backend.rs:1238-1244`). So the passes *are* wired, at the solver level.
Three things are true about that wiring, and each is a separate gap:

1. **It is off by default.** `SolverConfig::cnf_inprocessing` defaults to
   `false` (`backend.rs:375`), and `cnf_vivify` is a second, nested opt-in.
2. **It is preprocessing, not inprocessing.** It runs once, before the search
   starts. Nothing shrinks the formula again while the search is running, which
   is the half of Kissat's `probe` schedule that acts on a database already full
   of learned clauses.
3. **The certificate does not survive it.** When inprocessing is on, the DRAT
   proof is checked against `solve_formula` — the *reduced* formula — not the
   original encoding (`sat_bv_backend.rs:297`). No pass's DRAT is concatenated
   into the emitted stream. `vivify` is the only one of the three that even
   produces a `Vec<DratStep>`; `simplify` says so in its own module doc ("does
   not yet emit DRAT deletion steps (the proof-pipeline integration is a
   separate task)") and `bve` emits nothing at all.

So the honest statement of the gap is: **the passes exist, the proof-producing
core does not run them, and two of the three cannot yet say in DRAT what they
did.** Point 3 is the load-bearing one for this lane — a solver that
preprocesses and then emits a proof of the *preprocessed* formula has quietly
narrowed what its certificate certifies, and nothing in the pipeline announces
that.

Also worth writing down because it bounds the expected win: the boolean-core
measurements were taken through
`examples/boolean_core_profile.rs` → `solve_with_drat_proof_counted` on raw
DIMACS. That path has **no** preprocessing of any kind, so the 2.56x figure is
against a completely unreduced formula, and the headroom this lane is testing is
the full headroom.

## 2. Expectations, recorded before any measurement

Pre-registered so a later entry can be checked against them rather than
rationalised into them.

**E1 — the mechanism.** BVE is the pass that should move
propagations-per-conflict, not vivification or subsumption. The mechanism the
hypothesis names is "propagation cascades run over a smaller clause database",
and BVE is the only one of the three that removes *variables*; on bit-blasted
CNF the solver's own existing measurement records ~28% clause reduction from it
(`sat_bv_backend.rs:1046`). Subsumption removes redundant clauses that
propagation rarely visits twice; vivification shortens clauses without removing
propagation targets.

**E2 — the size of the effect.** I expect preprocessing to close **some** of the
2.56x and not all of it, because Kissat's advantage correlates with long runs
(the three files where our ratio is worst, 7.72 / 7.21 / 3.72, are exactly the
three where Kissat reached 259k-1.5M conflicts). A one-shot preprocess cannot
reproduce a formula that has been re-reduced fifty times. Point prediction:
**median propagations/conflict falls by 20-40%**, i.e. the 2.56x gap closes to
roughly 1.5-2.0x. I will be wrong in one of two directions and both are
informative: below 10% kills the hypothesis for the preprocessing-only form,
above 60% says the in-search half is not needed to get most of the win.

**E3 — the proof.** The dangerous failure mode is not a rejected proof, it is an
*accepted* one that no longer means what it did. Each pass's steps have to be
emitted in derivation order, with every `Add` before the `Delete` of the clauses
that justify it. My expectation is that all three passes are DRAT-expressible
with no RAT step and no extension variables — every clause any of them adds is
plain RUP:
- subsumption/tautology removal: pure `Delete`, unconditionally sound;
- self-subsuming resolution `C → C\{l}` with witness `D ∋ ¬l`, `D\{¬l} ⊆ C\{l}`:
  negate `C\{l}`, then `C` forces `l`, then `D` is falsified — RUP in two
  propagations;
- BVE resolvent `R = (C\{x}) ∪ (D\{¬x})`: negate `R`, `C` forces `x`, `D`
  falsified — RUP in two propagations;
- vivification: already emits RUP steps and already has tests.

**E4 — the cost of the certificate.** BVE *adds* resolvents, so the proof grows
by the number of resolvents, which on a wide bit-blasted CNF could be large.
The boolean-core lane measured DRAT logging at under 1% of search time at ~1.8
steps per conflict; a preprocessing prefix is a fixed one-time cost with no
conflicts to amortise it against, so I expect the prefix to be the *largest*
single block of the proof on instances that are decided quickly, and negligible
on instances that run to a conflict budget. I also expect **checking** to get
more expensive, not less, because deferred deletions keep the checker's active
set larger.

**E5 — where I most expect to be wrong.** That `simplify`'s multi-round
fixpoint has a step-order dependency I have not thought of: round 2's
strengthening witness may itself be a round-1 strengthened clause, so the steps
have to be emitted in the order the rounds produced them, not in clause-index
order over the final formula. A diff-based proof reconstruction (compare input
formula to output formula, emit the difference) would be *silently wrong* here
in exactly the way that produces an unverifiable proof for a correct verdict.
This is why the passes get instrumented rather than diffed.

## 3. Method

Fixed before the numbers, so the protocol is not chosen to suit them.

- The same eight p4dfa DIMACS the boolean-core lane used, identified by
  variable count from its table:
  `mobiledevice_bit8_na6_nr3_twocond` (31,482),
  `string1x8.4._bit8_na6_nr3_paired` (40,548),
  `mobiledevice_bit8_na6_nr3_paired` (58,380),
  `compose.s2._bit8_na6_nr3_paired` (106,588),
  `videoconf_full_bit8_na6_nr3_paired` (141,923),
  `string4x8.8._bit8_na6_nr3_paired` (256,789),
  `compose.s3._bit8_na6_nr3_paired` (473,949),
  `string4x16.4._bit16_na6_nr4_paired` (3,098,002).
- Host s5 (16 cores), idle, `taskset -c 0-7`, load recorded before and after
  every timing run. Arms interleaved; the two binaries confirmed to differ by
  sha256 before any number is believed.
- Fixed conflict budget, `SearchCounters` read from
  `solve_with_drat_proof_counted`. The headline metric is
  **propagations/conflict**; `propagations/s`, `conflicts/s` and the decided
  count are reported alongside it.
- Two runs minutes apart on this machine differ by up to ±20% on
  allocation-heavy work even at low load. Ratios and shapes are quoted, not
  figures to two significant places.

## 4. The code: proof-carrying preprocessing (ADR-1750)

`crates/axeyum-cnf/src/inprocess.rs` runs the enabled passes and streams their
`DRAT` derivation to the same sink the search will write to, so the
concatenation is one proof of the **original** formula. `simplify` and `bve`
gained crate-internal `*_recorded` variants that emit as they mutate;
`vivify` already emitted. `InprocessOptions::OFF` is the default and is
bit-for-bit today's behaviour: no pass runs, no step is emitted, and the two new
entry points reduce to the ones beside them.

**E3 held.** Every step every pass emits is plain `RUP`. No `RAT` step, no
extension variable, so nothing depends on a checker's `RAT` support or on the
pivot-literal convention. The three emission sites are:

* subsumption/tautology removal → `Delete(C)`;
* self-subsuming resolution `C → C \ {l}` with witness `D ∋ ¬l` → `Add(C \ {l})`
  then `Delete(C)`;
* BVE → `Add(resolvent)` for each, then `Delete` of every pivot clause.

**E5 was the right worry and the answer was to obey it, not to test around it.**
A proof reconstructed by diffing the input and output formulas has no ordering
guaranteed to verify, because `simplify` runs rounds to a fixpoint and a round-2
strengthening's witness can be a clause round 1 strengthened. The recorder is
threaded through `subsume_round` for that reason and no other.

### The first negative test was inverted, and the measurement said so

Pre-registered obligation 3 as "for each pass, drop one literal from a clause it
added and require the checker to reject" — over-strengthening being the
wrong-answer bug for every strengthening pass. First honest run:

```
pigeonhole-3-2 / bve: 11 of 12 over-strengthened mutants were ACCEPTED
```

Not a checker defect. The assertion was false, for two separate reasons, and
only the first was foreseeable:

1. On an unsatisfiable formula the prefix can drive the active set to
   inconsistency — BVE refutes small pigeonhole outright — after which *every*
   clause is `RUP` and a shorter one is a valid step. The mutation was producing
   a different valid derivation, not an unjustified one.
2. Restricting to **satisfiable** formulas, where 1 cannot happen, still left
   6 of 25 mutants accepted. That one is about the format: `check_drat` accepts
   `RUP` **or `RAT`**, and `RAT` is *satisfiability-preserving*, not
   entailment-preserving, so a clause that removes models can be a legitimate
   step. **A `DRAT` proof does not certify that each added clause was entailed.**

So the test as pre-registered was an inverted negative control — the "false"
case was true. It was replaced rather than weakened, and the replacement asks
the question the format answers.

### What the certificate does and does not depend on

Splitting the prefix into its `Add` half and its `Delete` half, and corrupting
each separately over the whole corpus, gives an asymmetry that is now asserted
in both directions rather than assumed:

| corruption | proofs built | rejected |
|---|---:|---:|
| **the passes stay silent about every clause they derived** (drop all `Add`s) | 38 | **38 (100%)** |
| **the passes emit no deletions at all** (drop all `Delete`s) | 38 | **0 — every proof still valid** |
| single-step over-strengthening (drop one literal from one `Add`) | 2,320 | 1,287 (55%) |

The first row is the defect this lane exists to prevent, and it is caught every
time, on every pass: a search running over clauses the checker was never given
cannot verify. The second row is not a gap: deletion only shrinks the checker's
active set and `RUP` is monotone in that set, so omitting deletions leaves a
strict superset of what the search saw. Two consequences worth stating plainly:

* **Only the clause-adding half of a pass is soundness-critical to record.** A
  pass that reduces purely by deleting — subsumption with no strengthening — is
  sound to run silently. It costs checking time, not correctness.
* Which means "we preprocessed and did not say so" is a soundness bug **exactly
  when the preprocessing derived something**, and is otherwise only a
  performance bug. The solver-side gap from section 1 is the dangerous kind:
  `sat_bv_backend`'s pipeline runs BVE, which derives resolvents.

### The soundness obligation, asked the way DRAT answers it

Since step-level entailment is not what the format carries, obligation 3 is
carried end to end instead: corrupt the pass's **output** (over-strengthen a
clause in the reduced formula *and* in the emitted prefix, as a buggy
strengthening would do both), search the corrupted formula, and require that
whenever this turns a satisfiable original into an `unsat`, the concatenated
proof is rejected.

**521 corruptions produced a wrong `unsat`. The checker rejected all 521.**

That number is asserted with a floor, because a run in which no corruption
produced a wrong verdict would have passed while checking nothing.

## 5. The measurement: the hypothesis survives, and it was under-predicted

Host s5 (AMD Ryzen 7 7840HS, 16 threads, 27 GB), idle, `taskset -c 0-7`, load
0.87 before and 1.03 after — the sweep was the only load. Binary
`ef8a80a3692329e0cbb82b40eece8b9da08d24e760075479df15b83fea17b6cc`, one build
for every arm, so no A/B can be confounded by a stale binary. Fixed
20,000-conflict budget, four arms (`off` / `subsume` / `bve` / `preprocess` =
subsume+BVE), two repeats with the arm order rotated per repeat, 64 cells, **0
failures**. The counters were bit-identical across repeats on every cell (the
driver checks and would have printed `NON-DETERMINISTIC`); the worst wall-time
spread across repeats was **1.025x**, so on this run the machine was quieter
than the ±20% the brief warns about. Figures below take the faster repeat.

### Propagations per conflict

| file | vars | `off` | `subsume` | `bve` | `preprocess` |
|---|---:|---:|---:|---:|---:|
| `mobiledevice_…twocond` | 31,482 | 734.5 | 914.9 | 435.3 | 589.9 |
| `string1x8.4` | 40,548 | 840.6 | 738.4 | 372.3 | 401.8 |
| `mobiledevice_…paired` | 58,380 | 966.1 | 953.6 | 411.6 | 355.8 |
| `compose.s2` | 106,588 | 1,828.1 | 1,713.9 | 896.9 | 1,060.9 |
| `videoconf_full` | 141,923 | 1,751.7 | 1,832.9 | 746.6 | 564.1 |
| `string4x8.8` | 256,789 | 2,435.5 | 1,792.1 | 829.6 | 913.6 |
| `compose.s3` | 473,949 | 4,271.9 | 4,961.5 | 2,460.7 | 2,562.6 |
| `string4x16.4` | 3,098,002 | 11,055.4 | 8,989.8 | 4,681.4 | 4,424.7 |

As a ratio to `off`, over the **six instances where every arm exhausts the
budget** (so all four arms analysed the same 20,000 conflicts and the ratio is
not confounded by one arm searching further):

| | `subsume` | `bve` | `preprocess` |
|---|---:|---:|---:|
| **median propagations/conflict vs `off`** | **0.933** | **0.426** | **0.388** |
| median over all eight | 0.962 | 0.435 | 0.439 |
| median conflicts/second vs `off` | 1.051 | **1.875** | **1.958** |
| median propagations/second vs `off` | 0.990 | **0.864** | 0.874 |

**The hypothesis holds, and E2 under-predicted it.** I predicted a 20–40% fall
in propagations per conflict and wrote that above 60% would say the in-search
half is not needed for most of the win. Measured: **57–61%**, at the top of
that band and past the point I nominated as surprising. Set against the
2.56x median deficit the boolean-core lane measured on the same eight files on
the same host, `2.56 × 0.426 = 1.09` — on this metric, one-shot BVE closes
essentially the whole gap to Kissat. The inprocessing hypothesis is the one that
survived contact with a measurement, after restart frequency and per-conflict
allocation did not.

**E1 was right about which pass, and by a wide margin.** Subsumption alone moves
the median 7% and makes it *worse* on three of eight files. Every bit of the
effect is BVE — the only pass that removes variables. `preprocess` (subsume then
BVE) is not reliably better than BVE alone: better on four files, worse on four.

**A mechanism the numbers volunteer, which I had not predicted.** Propagations
per *second* falls 13% under BVE. The reduced formula has **28% fewer clauses
but 18–21% more literal occurrences** (`cl_after/before ≈ 0.72`,
`lit_after/before ≈ 1.19`, uniform across all eight files): resolvents are
longer than the clauses they replace. So each propagation walks longer clauses
and costs more, and the 2.3x reduction in propagation *volume* is partly given
back as a 1.15x increase in propagation *cost*. Conflicts per second — the
product — still nearly doubles (1.88x). This is worth naming because it is the
same decomposition the boolean-core lane introduced, now cutting the other way:
a change aimed at volume moved rate too, in the opposite direction.

### What it costs, and where the trade turns

The other half of the result, and it is not favourable at this budget:

| file | `off` total | `bve` inprocess | `bve` search | `bve` total |
|---|---:|---:|---:|---:|
| `mobiledevice_…twocond` | 0.35 s | 1.23 s | 0.41 s | 1.64 s |
| `string1x8.4` | 0.96 | 2.39 | 0.54 | 2.93 |
| `compose.s2` | 2.74 | 3.59 | 1.52 | 5.11 |
| `videoconf_full` | 2.78 | 6.98 | 1.24 | 8.22 |
| `string4x8.8` | 4.24 | 12.26 | 1.43 | 13.69 |
| `compose.s3` | 9.75 | 20.67 | 5.40 | 26.07 |
| `string4x16.4` | 35.39 | 88.29 | 17.57 | 105.86 |

At a 20,000-conflict budget BVE loses on wall time on every file, by up to 3x,
because the pass costs 1.2–88 s against a search of 0.35–35 s. **That is a
statement about the budget, not about the pass.** The honest form is the
break-even: at what search length does the higher conflict rate repay the
one-time cost? `cost / (1/c_off − 1/c_bve)`:

| file | break-even conflicts | = seconds of unreduced search |
|---|---:|---:|
| `mobiledevice_…paired` | 73,366 | 4.6 s |
| `compose.s2` | 59,333 | 8.1 s |
| `videoconf_full` | 92,029 | 12.7 s |
| `string1x8.4` | 114,670 | 5.5 s |
| `string4x8.8` | 88,173 | 18.6 s |
| `compose.s3` | 95,995 | 46.6 s |
| `string4x16.4` | 100,846 | 176.9 s |
| `mobiledevice_…twocond` | 130,897 | 5.2 s |

**Strikingly flat in conflicts: 59k–131k on every file, median ~92k.** Both the
pass's cost and the search's rate scale with formula size, and they scale
together, so the break-even lands in the same place across a 100x range of
instance size. The 20,000-conflict budget this sweep used is a factor of ~4.6
below it — which is why the wall-time column looks bad and why it should not be
read as the verdict on the pass.

In seconds it is not flat at all, because the unreduced conflict rate is not:
4.6 s on a 58k-variable instance, 177 s on the 3.1M-variable one. Set against
the gate-b public-slice budget of 20 s, BVE is at or past break-even on the
small and middle instances and nowhere near it on the largest.

**Decided counts at the 20,000-conflict budget: `off` 1 of 8, `subsume` 1,
`bve` 1, `preprocess` 2 of 8** (`preprocess` additionally decides `compose.s2`
`sat`). One instance is not a result; it is reported because the brief asks for
it and because a budget this far below break-even is not where a decided-count
difference would show up.

### The certificate: E4 was right and the magnitude is worse than "large"

| file | `off` proof steps | `bve` prefix steps | `bve` total |
|---|---:|---:|---:|
| `mobiledevice_…twocond` | 14,271 | 340,166 | 362,928 |
| `compose.s2` | 35,558 | 1,240,294 | 1,275,553 |
| `string4x8.8` | 36,310 | 3,005,783 | 3,041,202 |
| `string4x16.4` | 36,474 | **37,702,624** | 37,737,995 |

The search emits ~36,000 steps at a 20,000-conflict budget regardless of
instance size (1.8 steps per conflict, as the boolean-core lane measured). The
BVE prefix is proportional to the *formula*, so on the largest instance it is
**1,034x the search's proof**. Two consequences:

* The in-RAM `VecProofSink` is not viable for a BVE prefix at this scale — 37.7 M
  steps is the shape that OOM-killed a run at 27.6 GiB before. The streaming
  sink (ADR-0381) is not an option here, it is the only option. `inprocess_into`
  drains to the sink one pass at a time for the same reason, but one pass's
  derivation is still the whole prefix.
* Subsumption's prefix is three orders of magnitude smaller (92,232 steps on the
  same file) because it only deletes. Which is the earlier asymmetry again, now
  in bytes rather than in soundness: the pass that derives nothing costs the
  certificate nothing.

### The proof still checks, at a scale beyond the unit corpus

The eight `p4dfa` instances are the wrong fixture for this: **none of them is
decided `unsat` within the budget**, and a sweep over the whole ≤25 MB slice
found no `p4dfa` instance the native core refutes at 20,000 conflicts, so there
is no `p4dfa` proof to check. Recorded as a limitation, not worked around.

A near-threshold random 3-SAT instance (240 variables, 1,056 clauses, seed 11)
is refuted and gives a real proof at scale, on s4:

| arm | verdict | proof steps | `check_drat_backward` | `check_drat` (forward) |
|---|---|---:|---:|---:|
| `off` | unsat | 203,528 | 0.87 s → `Ok(true)` | 200.85 s → `Ok(true)` |
| `preprocess` | unsat | 194,428 | 0.98 s → `Ok(true)` | 193.71 s → `Ok(true)` |

Both check against the **original** formula. Two things worth keeping:

* **Forward checking is 231x and 199x slower than backward here** — far past the
  26x the boolean-core lane measured on its 757-step pigeonhole fixture, and in
  the same direction. Forward `check_drat` is quadratic-ish in the proof length
  and is not the route for a corpus-scale certificate; the integration suite uses
  it deliberately because on 19 tiny fixtures the stricter, simpler checker is
  the right one.
* E4 predicted checking would get *more* expensive with inprocessing on. On this
  instance it did not — the proof is 4% shorter and both routes are within a few
  percent. The prediction was about the deferred-deletion design I did not end
  up building (deletions are emitted in place, per pass), so it was answering a
  question about a version of the code that does not exist.

## 6. What this lane did not do

- **In-search inprocessing.** Everything above is *pre*-processing: one pass
  before the search starts. Kissat's `probe` schedule also runs while the search
  is running, over a clause database already full of learned clauses, and that
  half is **not run here — not ruled out**. It needs `Cdcl` to rebuild its
  arena, headers and watch lists at level zero while preserving VSIDS activity
  and saved phases, which is a real change to the search loop rather than a
  wrapper around it. The measured break-even of ~92k conflicts is the number
  that makes it interesting: a schedule that re-reduces every ~100k conflicts is
  paying roughly what a single pre-pass pays, for a formula that keeps shrinking.
- **Flipping any default.** `InprocessOptions::OFF` remains the default on every
  entry point. At the budgets measured here inprocessing loses on wall time, and
  turning it on by default would be choosing a number this sweep did not
  measure. The break-even table is what a scheduling decision should be built
  on, and building it is the next slice, not this one.
- **The solver-level gap from section 1.** `sat_bv_backend` still checks its
  `unsat` proof against the *reduced* formula (`sat_bv_backend.rs:297`,
  `ensure_unsat_proof_checked`), so with `cnf_inprocessing` on the BVE link is
  trusted rather than checked. Not unsound — BVE preserves equisatisfiability,
  so the chain holds — but the checkable artifact covers one link of it, which is
  exactly the shape [ADR-1721](../09-decisions/adr-1721-a-preprocessing-step-owes-one-of-three-obligations-chosen-by-the-direction-it-can-break.md)
  names. The machinery to close it now exists (`solve_with_drat_proof_inprocessed`
  against the pre-inprocessing formula); the obstacle is that the backend also
  `compact()`s, which renumbers variables and so breaks the correspondence
  between the emitted prefix and the formula the search ran on. Left as the named
  follow-up rather than attempted, because it is a second crate with its own
  golden pins.
- **CaDiCaL, and Kissat re-run under this change.** The comparison here is
  against the boolean-core lane's Kissat figures on the same eight files and the
  same host, not against a fresh Kissat run. Kissat was not re-run.
- **Memory.** Every number here is time or a count. The 37.7 M-step prefix was
  produced under a 20 GB ceiling and did not hit it, which is the only memory
  fact this sweep establishes.
