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
