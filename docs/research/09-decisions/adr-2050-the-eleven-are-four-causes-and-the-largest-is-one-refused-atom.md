# ADR-2050: the eleven are four causes, the largest is ONE refused atom, and one of them is not a ground-checker gap at all

Status: accepted
Index-summary: [ADR-2040] and [ADR-2035] converged on "a small set of quantifier-free queries that cvc5 **and** z3 both refute and we cannot", 11 `CAPABILITY-LIMIT` rows. This lane takes all 13 and answers what each one NEEDS. **The 11 re-derive exactly** on the current tree (11 `CAPABILITY-LIMIT` / 2 `DECIDED`, matching [ADR-2040] row for row), so the inherited list does NOT overstate — unlike [ADR-2035]'s 8-of-22. **They are FOUR causes, not eleven, and not one.** (A) **Six rows, all `AUFLIRA`, are ONE refused atom**: `lira-dpll` declines the WHOLE query the moment `lra.rs::linearize` meets a subterm it cannot linearize — a `select`, or an application of `log`/`divide`, which in `AUFLIRA` are *declared* functions and therefore just opaque Real terms. The refusal is **2 to 4 atoms per file**. The integer mirror of exactly this capability ALREADY SHIPS (`IntCollector::allow_opaque_apps`, "sound for UNSAT transfer"); the Real collector has `vars: Vec<SymbolId>` and so structurally cannot hold a term. Simulated OUTSIDE the solver by replacing only the atoms `linearize` rejects with opaque Bools: **6 of 6 flip `unknown` → `unsat`, 3 passes per arm, 6/6 STABLE-GAIN**, with z3 AND cvc5 confirming `unsat` on the abstracted query at a full 6/6 comparable denominator, and a **non-vacuous** negative control (a satisfiable query, 31 atoms opaqued, stays `sat` through the same instrument). (B) **Two rows are SELECTION, not capability**: we refute a 3-conjunct subset of 268 and a 1-conjunct subset of 633 **in 24 s**, and fail on the whole — [ADR-2020]'s open axis, reappearing with a concrete witness. (C) **Two rows are a SILENT HANG**: the watchdog fires with **no route line at all**, at 24 s and at 120 s, **even on the minimal core** — [ADR-2040] §8's unsplit `bound_by=NONE` bucket. (D) **One row is not a ground-checker gap**: we refute its quantifier-free skeleton, standalone, in under 24 s (`euf-online`), yet [ADR-2040] scored the file `CAPABILITY-LIMIT` — so the rung is not handing the ground checker the query the census's abstraction describes. Every row's minimal unsat subset is **ONE conjunct** (f02 is 3), median 1 against a pre-registered prediction of ≤ 5. **A method correction this lane published against itself**: its own first commit called one row an instrument artefact because `abstract-quantifiers.py --fresh-per-occurrence` returns `sat` where the shared-by-text map returns `unsat`. That inference is invalid — no-sharing is strictly WEAKER than correct sharing, so its `sat` cannot refute anything — and the conclusion was false: a third instrument that shares only AFTER `let`-expansion (sound, and still sharing) says `unsat` at 11 of 11 measurable rows, 0 `NOT-ADMISSIBLE`. **The documented control could not decide its own question**, which is the transferable finding. **No lever was built** (pre-registered R10): the change is bounded and named, but it is new public route surface with sat-side soundness obligations, and the +6 is a SIMULATION, not a measurement of shipped code. Also: the two reach levers [ADR-2040] ships `Off` are load-bearing for 3 of 13 rows, which are refused at INGEST without them.
Index-status: accepted
Date: 2026-09-14

## Context

Eleven lanes worked the quantified divisions this week and closed every
hypothesis about quantifier *handling*. What they converged on, stated twice
independently, is a ground question:

> **[ADR-2040] §5**: with both reach fixes armed, all 13 skeleton-shaped rows
> reach the rung and split at 24 s **and** at 5x: **11 CAPABILITY-LIMIT / 2
> CONVERTED / 0 BUDGET-LIMIT / 0 RUNG-NEVER-REACHED.** The remaining 11 are the
> ground checker refusing a **quantifier-free** query two independent solvers
> refute.

That is the purest capability question available and it is small enough to
answer completely rather than statistically. This lane answers it.

Branch base: `git merge-base main HEAD` is
`cfcae7fa78bbc8297ccb62d8517895edb87d8c33`, which **is** local `main`'s HEAD.
Rules were [pre-registered](../../../bench-results/qf-wall-20260914/PREREGISTRATION.md);
that file states plainly which phase preceded it and which rules it governs.

## 1. The population re-derives exactly, and that is worth saying

R1 exists because [ADR-2035] found **8 of 22** censused "declining" files were
decided anyway, so an inherited list overstates by more than a third. Re-run
here on the current tree, on the ORIGINAL benchmark files, both reach levers
armed (the condition [ADR-2040] measured), at 24 s and at 120 s:

| | n | [ADR-2040] | here |
|---|---:|---:|---:|
| `CAPABILITY-LIMIT` | 11 | 11 | **11** |
| `DECIDED` / `CONVERTED` | 2 | 2 | **2** |

**Row for row, not just in total.** `ref/rederive.tsv`. The inherited list does
not overstate. A re-derivation that CONFIRMS is a weaker headline and the same
amount of evidence, and R1 does not get to be run only when it is expected to
pay.

**The reach levers are load-bearing and they ship `Off`.** With
`AXEYUM_DISTINCT_LINEAR` unset, 3 of the 13 rows (`f07`, `f10`, `f13`) are
refused at INGEST — `` `distinct` with 422 arguments requires 88831 pairwise
expansions `` — and never reach any route at all; `f13` goes from `unknown` to
`unsat` when it is armed. Any measurement of this population taken on the
shipped default is measuring the ingest cap on 3 of 13 rows.

## 2. The admissibility question, and a correction this lane owes itself

[ADR-2040]'s 13 come from `abstract-quantifiers.py` in its **default**
shared-by-text atom map. That tool's own docstring says the map is **not
unconditionally sound** — `let` can bind one name to two values, so identical
text can denote different formulas, and forcing them equal STRENGTHENS the
skeleton and could manufacture a false `unsat` — and it names
`--fresh-per-occurrence` as the control. `skel-census.sh` never passes the flag.
The control was never run.

Running it: 12 of 13 agree; `UF/sledgehammer/Fundamental_Theorem_Algebra/
uf.1065126.smt2` disagrees, shared `unsat` versus fresh `sat`, under z3 and
cvc5, and it carries **114 `let` forms**.

**This lane's first commit (`2af00d4b2`) called that an instrument artefact. That
was wrong, and the error is worth more than the claim was.** Fresh-per-occurrence
shares *nothing*, so it is strictly **weaker** than any correct sharing. Its
`sat` establishes only that some sharing is load-bearing. It cannot establish
that the sharing was unsound, and reading it that way is reading a weaker
abstraction's `sat` as a refutation of a stronger one's `unsat`.

`scopeskel.py` is the instrument that decides: expand every `let` first, then
share an atom between two quantified subformulas exactly when they are
**structurally identical after expansion** — at which point no binder remains
that could give one text two meanings, so the sharing is sound *and* it still
shares.

| atom map | sound? | shares? | can it decide admissibility? |
|---|---|---|---|
| shared-by-text (the census) | no | yes | no — this is the claim under test |
| `--fresh-per-occurrence` (the documented control) | yes | **no** | **no** — strictly weaker, so its `sat` refutes nothing |
| structural-after-`let`-expansion (`scopeskel.py`) | yes | yes | **yes** |

Over all 13: **11 ADMISSIBLE, 0 NOT-ADMISSIBLE, 2 DID-NOT-RUN** (`f07`, `f10`;
§6). On the contested row it is `unsat` under z3 **and** cvc5 at 428
occurrences and 324 atoms — the same counts as the text map. **The census's 13
stands.**

**The transferable finding is not about this row. It is that the control a tool
documents for itself was not able to decide its own question**, and a lane that
runs it and stops has a disagreement it will read as a defect. A control that
can only ever flag a row for a third test should say so where it is documented.

## 3. Every one of these queries is ONE conjunct

Before asking what capability a refutation needs, ask how much of the query the
refutation uses. `minimize.py` splits every top-level `and` (an equivalence, and
the split file's `unsat` is re-checked before anything else runs), takes z3's
unsat core, then deletes core members one at a time while the remainder stays
`unsat`.

| | conjuncts after splitting | z3 core | minimal |
|---|---:|---:|---:|
| the six `AUFLIRA` rows | 14 | 1 | **1** |
| `UFNIA` `TwoSquares` | 268 | 3 | **3** |
| `UFLIA` `StandardPrettyPrint` | 633 | 1 | **1** |
| `UFNIA` `verisoft-baby` / `spec_sharp` | 3 | 1 | **1** |
| `UFNIA` `usbsamp` ×2 | 682 | 2 | **1** |

**Median 1**, against a pre-registered prediction of ≤ 5 (P4, right). Four of
the six `AUFLIRA` minimal cores are a **propositional** contradiction — a
conjunction containing both `p` and `¬p`, or an antecedent containing the atom
its consequent needs. The other two add exactly one arithmetic step: `x ≥ 1 ⊢
x > 0`, and `x ≥ 2 ⊢ x ≥ 0`.

Nothing in this population is hard. That is what makes it the right population.

## 4. The eleven are FOUR causes

Measured per row on the standalone quantifier-free query — no quantifiers, no
rung, no instantiation, no budget split (`ref/scope-ax.tsv`, `ref/trails-armed.txt`,
`ref/coretable.tsv`).

### (A) ATOM-REFUSAL — six rows, all `AUFLIRA`, and it is ONE site

All six carry the same trail line and nothing else distinguishes them:

    {"route":"lira-dpll","outcome":"declined","reason":"unsupported",
     "detail":"lazy arithmetic: unsupported arithmetic atom:
               QF_LRA: non-linear or non-real subterm in a constraint"}

`dpll_lia.rs::ArithAbstractor::abstract_term` calls `ensure_supported_atom` on
every atom; on `Err` it returns `Err`, which **refuses the whole query**. The
guard is deliberate and has a test saying so: *"unsupported arithmetic atoms
must not enter the Boolean skeleton."*

What the refused subterms actually are:

    (declare-fun log (Real) Real)
    (declare-fun divide (Real Real) Real)
    (declare-fun s_values7 () (Array Int Real))

`AUFLIRA` has no transcendental theory, so `log` and `divide` here are
**declared** functions — plain uninterpreted Real terms — and `(select
s_values7 i)` is an array read of Real sort. Every one of them is a perfectly
good *leaf* of a linear constraint. `lra.rs::linearize` ends in a bare

    _ => Err(unsupported("non-linear or non-real subterm in a constraint"))

**and the integer mirror of exactly this capability already ships.**
`IntCollector` carries `allow_opaque_apps`, `opaque_var_index: BTreeMap<TermId,
usize>` and `index_of_opaque`, with one match arm mapping an `Op::Apply` of Int
sort to a fresh opaque integer variable, documented as *"sound for UNSAT
transfer: the abstraction is a relaxation."* The Real `Collector` has
`vars: Vec<SymbolId>` and `var_index: BTreeMap<SymbolId, usize>` — keyed by
SYMBOL, so it structurally cannot hold a term.

**How many atoms are refused per file: 2, 2, 2, 3, 4, and 27.** A two-atom
refusal discards a 14-conjunct query whose refutation is propositional.

### (B) SELECTION — two rows, and we refute the core in 24 s

| row | conjuncts | our verdict on the whole | our verdict on the minimal core |
|---|---:|---|---|
| `UFNIA/sledgehammer/TwoSquares/z3.861593` | 268 | `unknown` | **`unsat`** |
| `UFLIA/simplify2/…/StandardPrettyPrint.008` | 633 | `unknown` | **`unsat`** |

Both die on the same bound — `` eager Ackermann elimination would emit 131 ``
(resp. `59282`) `` congruence constraints, exceeding the deterministic
admission bound of 64 `` — and on the second also on the pre-SAT skeleton
envelope (`atoms=19240, cnf_vars=39517`). Hand us the three conjuncts that
matter and we refute in well under the budget. **This is [ADR-2020]'s open axis
— the SIZE of the ground set, and selection — now with a named witness whose
answer we provably already have.**

### (C) SILENT HANG — two rows, at 24 s and at 120 s, even on the core

`usbsamp_bug_example_2_3_8_1` and `usbsamp_example_2_3_4_0`:

    ; give-up kind=Watchdog detail=watchdog fired before the worker thread returned

No route line. Not at 24 s, not at 120 s, and **not on the minimal core**
either. This is [ADR-2040] §8's unsplit `bound_by=NONE` bucket — named there as
the second-largest unexplained one and untouched — reproduced here on a single
444 KB conjunct, which is a far smaller reproducer than the benchmark.

### (D) NOT A GROUND-CHECKER GAP — one row

`UF/sledgehammer/Fundamental_Theorem_Algebra/uf.1065126`. Handed its
quantifier-free skeleton directly, **we refute it**, `unsat`, inside 24 s, via
`euf-online`, on the scope-correct abstraction as well as the text one.
[ADR-2040] scored the file `CAPABILITY-LIMIT`.

Both are correct measurements of different things, and the gap between them is
the finding: **the rung is not handing the ground checker the query the
census's abstraction describes.** Whatever the rung abstracts to, our own
ground checker decides the census's version of it. That is a wiring or
granularity question, not a capability one, and it is not answered here.

### The tally

| cause | rows | what it is |
|---|---:|---|
| **(A) ATOM-REFUSAL** | **6** | one `Err` return, one named site, Int mirror already ships |
| (B) SELECTION | 2 | we already refute the core |
| (C) SILENT HANG | 2 | watchdog, no route line, unreduced |
| (D) not a ground gap | 1 | the rung's own abstraction |

**Four, not eleven — and not one.** (A) is 6 of 11, Wilson 95 % `[31.3 %,
83.2 %]`, which with n = 11 is exactly as wide as it should be and is quoted
rather than hidden.

## 5. (A) simulated outside the solver, before writing a line of it

`opaqueatom.py` builds the query the proposed change would hand the Boolean
skeleton: an atom whose leaves are numerals and nullary arithmetic symbols is
left alone, and every other atom becomes one fresh `Bool` shared by structure.
Its notion of "linearizable" is copied from `lra.rs::linearize` and is
deliberately narrower, so it can only UNDERSTATE.

**On the FULL quantifier-free skeleton — not the minimal core:**

| row | atoms kept | atoms opaqued | before | after | z3 | cvc5 |
|---|---:|---:|---|---|---|---|
| `quaternion_ds1_inuse_0013` | 5 | 27 | `unknown` | **`unsat`** | `unsat` | `unsat` |
| `gauss_init_0292` | 42 | 4 | `unknown` | **`unsat`** | `unsat` | `unsat` |
| `gauss_array_0490` | 8 | 2 | `unknown` | **`unsat`** | `unsat` | `unsat` |
| `gauss_array_0289` | 10 | 2 | `unknown` | **`unsat`** | `unsat` | `unsat` |
| `gauss_array_0013` | 10 | 2 | `unknown` | **`unsat`** | `unsat` | `unsat` |
| `gauss_array_0390` | 10 | 3 | `unknown` | **`unsat`** | `unsat` | `unsat` |

**6 of 6.** Three passes per arm on every moved row: **6/6 STABLE-GAIN**, 0
UNSTABLE, 0 FLIP. R6, three authorities: z3 and cvc5 both `unsat` on all six
abstracted queries at a **comparable denominator of 6/6 on each**, no
abstentions — six agreements, not six no-opinions. Abstraction is a weakening,
so `abstract unsat` entails `skeleton unsat`, which entails `original unsat`,
and that is the only direction claimed.

**The negative control, and it is non-vacuous.** The soundness of opaque-atom
abstraction is an argument. What an argument cannot establish is that the
script built the formula it claims to have built — a parser bug that dropped
assertions makes everything `unsat` and every row "converts". So a
**satisfiable** ground query goes through the same instrument: **31 atoms
opaqued** (so the instrument fired), and z3, cvc5 and axeyum all still say
`sat`. The control has somewhere to fire and it fires; the zero is not the
[ADR-2040]-style weak kind.

**The instrument lied once and the control caught it.** Its first version
rewrote `(set-logic AUFLIRA)` to `(set-logic ALL)`. `ALL` carries `log` and
`exp` as theory symbols, these benchmarks legally *declare* them, and cvc5
rejects a declaration shadowing a theory symbol in scope — so the cvc5 column
was a parse error on 3 of 4 rows and the authority check was measuring the
rewrite. The logic line is now kept verbatim.

**One more mechanism result worth recording**: the abstracted `gauss_array_0490`
is decided by `dl-online`, not by `lira-dpll`. On the unmodified query
`dl-online` declines `not-applicable`, because non-DL atoms are present. So the
same capability unlocks a route EARLIER in the ladder than the one that
refuses, and a fix confined to `ArithAbstractor` is not obviously the whole of
it. That is an open design question and it is the reason §6 does not treat the
sizing as settled.

## 6. Decision: characterise, do not build

Pre-registered **R10**: no lever is built unless step 3 names ONE capability
and its site is bounded. Step 3 names one capability covering 6 of 11 rows, and
its site is bounded — `lra.rs`'s Real `Collector`, `dpll_lia.rs`'s
`ensure_supported_atom`, and the `Sat`-to-`Unknown` downgrade the integer side
already performs at `lra.rs:2260`.

**It is still not built, and the reason is stated rather than folded in.** The
change makes a new weakened query reachable by the ladder, which is new public
route surface; `CLAUDE.md`'s standing rule is that semantics and model lifting
are explicit *before* such surface exists. The sat side is the whole risk: every
exit that could return `Sat` on a query carrying an opaque atom must return
`Unknown`, and §5's last paragraph shows the abstraction is consumed by a route
(`dl-online`) that is not the route that refuses, so "every exit" is not yet an
enumerated set. **The +6 in §5 is a SIMULATION run outside the solver. It is not
a measurement of shipped code and must not be quoted as one.**

What the next lane is handed: the named site, the Int-side precedent to mirror,
the exact atoms refused per file, a committed simulation with its control, and
one open design question (in-abstractor versus a ladder rung). What it owes
before shipping `On`: R9's gate — ≥ 4 rows net, 0 losses, 0 flips, every moved
row STABLE-GAIN over 3 passes per arm, 0 authority disagreements — on an
interleaved per-file A/B with a published noise floor.

**Predicted post-merge value: no division total moves.** This ADR lands
documentation, instruments and result tables; no `crates/` file is touched.
That is a prediction about a no-op, and it is worth stating because prediction
is the discipline, not because the answer is interesting.

## 7. The rules, against what happened

| rule | pre-registered | outcome |
|---|---|---|
| R1 | the inherited list is re-derived before it is counted | §1 — 11/2, row for row. It did NOT overstate |
| R2 | the ABSTRACTION is re-derived too; an unsound-map row is INADMISSIBLE | §2 — and the rule fired against this lane's own first conclusion, which was wrong |
| R3 | every bucket with its denominator; NOT MEASURED separate from zero | §4, §6 — `f07`/`f10` are `DID-NOT-RUN` in §5 and counted in no bucket there |
| R4 | capability claims by MECHANISM, not verdict counts | §4 (trail lines + the two collectors' types), §5 (one solver, two queries, one axis) |
| R5 | every weakening stated with its direction and checked | §2, §5. The one instrument that could STRENGTHEN is the one §2 is about |
| R6 | three authorities, comparable denominator beside any zero | §5 — 6/6 on z3 and 6/6 on cvc5, no abstentions |
| R7 | Wilson 95 % on every proportion | §4 |
| R8 | interleaved A/B discipline if a lever is built | **not reached** — no lever. The 3-passes-per-arm and non-vacuous-control halves were run anyway on the simulation (§5) |
| R9 | ship `On` only at ≥ 4 net with 0 loss/flip/disagreement | **not reached** — nothing to ship |
| R10 | no lever unless step 3 names ONE bounded capability | §6 — the condition is met and the lane still declines, with its reason |
| R11 | the measurement is of THIS BRANCH; post-merge predicted | §6 |
| R12 | freshness by `find -newer`, not exit status | `build.sh`; the binary is `ea0fceaf…` at `cfcae7fa7` |
| R13 | no waiter greps for a process by a pattern its own command line contains | every waiter here watches an artifact or runs in the foreground |
| R14 | unfinished checks reported as "did not run" | §8 |

**The predictions, against what happened:**

| | predicted | measured |
|---|---|---|
| **P1** | fewer than 13 survive R1+R2; ≥ 1 INADMISSIBLE | **WRONG.** 13 survive, 0 INADMISSIBLE. The row that looked inadmissible was this lane misreading its own control (§2) |
| **P2** | 1–3 named capabilities cover ≥ 6 of the 11 | **right** — ONE covers 6 |
| **P3** | ≥ 1 row's refutation needs no theory solver at all | **right** — four of the six `AUFLIRA` minimal cores are propositional |
| **P4** | minimal subsets small, median ≤ 5 conjuncts | **right, and stronger** — median **1** |
| **P5** | the `AUFLIRA` six behave as one family | **right** — identical trail line, identical cause, 6/6 in simulation |

P1 is the useful one to have got wrong. It was written expecting the inherited
list to overstate, because the last lane's did; it did not, and the lane then
manufactured an overstatement out of a control it had misread. **A
pre-registered prediction that something will shrink is a standing invitation to
find shrinkage.**

## 8. Not measured here, and reported as "did not run"

- **`f07` and `f10` have no abstraction of any kind.** Every instrument here
  expands `let` first, and those two files are 724 KB / 732 KB with **107
  nested `let` bindings**; expansion is exponential in the nesting and does not
  finish in bounded memory. They are `DID-NOT-RUN` for §2's admissibility,
  §5's simulation and the propositional column, and are counted in no
  denominator there. What IS known about them is in §4(C), from the trail.
- **The lever is not built and therefore not A/B'd.** §6.
- **Cause (C) is not diagnosed.** Which route hangs without emitting a trail
  line is not answered; a 444 KB single-conjunct reproducer now exists.
- **Cause (D) is not diagnosed.** Why the rung's own abstraction does not reach
  what our ground checker decides standalone is not answered.
- **Nothing outside these 13 files was measured.** The corpus rate of cause (A)
  is unknown; six `AUFLIRA` rows out of a 36-row undecided division is not a
  corpus rate and R1 forbids transferring it.
- **An `ulimit -v` is now set by every script here that expands a `let`.** The
  first run without one reached **63.4 GB resident** and the kernel OOM-killer
  fired globally on the dev box, killing the session.
  `scripts/cargo-serialized.sh` bounds cargo; nothing bounds a lane's own
  Python. A ceiling only converts the crash into a `MemoryError`, so the two
  files are additionally skipped **by name**.

[ADR-2020]: adr-2020-the-ground-checker-mostly-refuses-and-the-set-it-refuses-is-one-we-had-no-need-to-build.md
[ADR-2035]: adr-2035-two-populations-reach-one-boundary-and-a-round-cap-can-convert-neither.md
[ADR-2040]: adr-2040-the-reach-half-is-worth-two-and-the-whole-remaining-shape-is-the-ground-checker.md
