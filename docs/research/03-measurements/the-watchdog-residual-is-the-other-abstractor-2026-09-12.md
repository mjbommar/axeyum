# The watchdog residual is the OTHER abstractor

**2026-09-12, lane `watchdog-residual`.** Follow-on to
[watchdog-kills-are-a-deadline-blind-phase](watchdog-kills-are-a-deadline-blind-phase-2026-09-12.md)
(`47f902ea1`). That note fixed two deadline-blind phases and closed with a
hypothesis about the residual. **The hypothesis was wrong**, and so was the
method that produced it — which is the more useful half of this note.

## The closing hypothesis, and why it could not have been right

It said the residual was `lra::solve` (Fourier–Motzkin) "on a path whose
deadline is still `None` above it — one more constant to find." On merged main
`lra::solve` takes a deadline, polls it in both loops, and its one production
caller passes a real one. There was no such constant.

The hypothesis came from a `perf` profile: Fourier–Motzkin was 21% of the
samples, `memmove` 35%. Both numbers are true. A profile says where the
*cycles* are; the question a watchdog kill asks is where the *budget* is, and
those differ whenever a cheap phase calls an expensive one in a loop. Here they
differed completely: Fourier–Motzkin was hot because something above it was
calling it 540 times, and that something was neither slow nor deadline-blind in
itself.

## The instrument: a stack written on entry

Everything in this tree records at a boundary a stage has already crossed —
`RouteTrace` on decide/decline, `LazySmtCounters` at the end of a round,
`BvStageMirror` when a stage finishes. So a killed run's last word is always the
name of something that had already finished. On
`cpachecker-induction.minepump_spec1_product56…` the trail ended with `nra`
declining at **38 ms** and then said nothing for 25 seconds.
`RouteTrace::open_segment` could say the 25 s existed. Nothing could say what
was in it.

`crate::phase_breadcrumb` is a stack pushed on ENTRY and popped on return,
behind an `Arc` on the `live_instruments` board, so the watchdog thread reads it
while the worker is still inside the frame. `smtcomp_cli` prints it as
`; partial phase …` right under `; partial route-open`.

It found the phase in four readings, each one a rebuild away:

| reading | `in=` | what it said |
|---|---|---|
| 1 | `euf:uf-arith-lazy` (12.9 s) | the lazy UF+arithmetic CEGAR, not `nra` as the trail implied |
| 2 | `euf:fc-round-solve` | inside round 1 of the congruence loop, `enters=lra:decide:540` |
| 3 | `dpll-lia:abstract` (call **2**) | inside the Boolean abstraction, which never finished |
| 4 | `stack=none`, `depth=0` | the euf route now RETURNS; the budget moved elsewhere |

Reading 4 is the shape worth naming: an empty stack with live `enters=` counts
is not a failed reading. It says the worker was outside every instrumented
phase, which is a fact about where to put the next frame.

## Defect 1 — a membership question answered by running a decision

`dpll_lia::ArithAbstractor::order_atom` admits an atom by calling
`ensure_supported_atom`, which ran `check_with_lra(arena, &[atom])` — a whole
conjunctive decision, collection then Fourier–Motzkin or the exact-rational
simplex — and then **discarded the verdict**. It reads exactly one bit of that
answer: did it come back `Unsupported`?

Every `Unsupported` either route can raise comes from its collector. In `lra.rs`
the four sites are the real disequality, the non-conjunctive fall-through, the
nonlinear multiplication and the non-linear-term fall-through, all inside
`Collector::collect` / `Collector::linearize`; every arm of `decide_within` past
collection returns `Ok(Decision::…)`, and its only `Err` is a
`SolverError::Backend` replay alarm. The integer side is the same shape. So the
search after collection could never change the answer.

`47f902ea1` had already memoised this call, cutting it from 11,236 decisions to
one per distinct atom. That is the right guard and it was not enough: **540
distinct atoms is still 540 whole decisions**, 539 of them reaching
Fourier–Motzkin, inside one abstraction build that the watchdog then killed.

Fixed by `lra::atom_in_lra_fragment` / `lra::atom_in_lia_opaque_fragment`, which
run the collector and stop. `lra:certified` 540 → 1, `lra:fm-solve` 539 → 0.

## Defect 2 — the same DAG tree-walk, in the abstractor nobody looked at

`dpll_t::Abstractor::abstract_term` was memoised in `c4046c2d6`. That is the
abstractor the **`nra` route** reaches. The `euf` lazy-UF+arithmetic route —
which is where 49 of `QF_UFLRA`'s 51 watchdog files actually are — goes through
`dpll_lia::ArithAbstractor`, a *different* struct with the same defect:
unmemoised recursion over an assertion DAG, i.e. a tree walk, exponential in the
sharing.

`ArithAbstractor` has an `atom_of: HashMap<TermId, SymbolId>` and it was easy to
read that as the memo. It is not. It caches the **leaves**; the sharing lives in
the Boolean structure above them, which was rebuilt once per path.

Fixed by a `memo: HashMap<TermId, TermId>` and a wrapper, exactly as `dpll_t`
does. A timed-out walk is never cached: it returns a `false` constant standing
for "we stopped", and caching that would make the placeholder permanent.

## Defect 3 — `IncrementalArithDpll::new` hardcoded `None`

ADR-1906's shape a third time, in the argument rather than the counter.
`check_with_incremental_arith` — inside the CEGAR round, with the round's
remaining budget in its hand — called `IncrementalArithDpll::new`, whose whole
body is `new_with_deadline(arena, assertions, None)`. So the abstraction build
consulted no clock while its caller had a real deadline three frames up, and
"the round checks its budget before it starts" bounded nothing at all. `new` is
gone; `new_within` takes the deadline and the caller passes it.

## What the fix does and does not do

On `minepump_spec1_product56` at a 24 s budget, the `uf-arith-lazy-overbound`
route now **runs to 17,998 ms and declines in good order** with
`reason=budget` — the route that used to consume the budget invisibly now
returns `Unknown(ResourceLimit)` with a reason that names its own state
(`total_rounds=6, atoms=562, blocking_lemmas=6, min_oracle_calls=1120`). Ten
abstraction calls complete where two did not. The file is still `unknown`: the
remaining ~6 s goes to a route after `euf-online` that has no frame yet, which
is the next reading to take rather than a conclusion.

## The A/B, and the flake it caught

Interleaved per-file against `47f902ea1`: both arms back to back on the **same
pinned core**, arm order alternating by file index, 24 s budget. Population:
every watchdog file in `QF_UFLRA` (51), `QF_LIA` (28) and `QF_IDL` (19), plus a
60-file control of files the board records us deciding — **158 pairings**.

| | before | after |
|---|---:|---:|
| watchdog kills (wall ≥ 24.9 s) | 92 | **81** |
| newly killed | — | **0** |
| verdict regressions over all 158 | — | **0** |

Of the 11 files that stopped being killed, **4 came back with a verdict** and 7
now return `unknown` INSIDE the budget (16.65–24.48 s) instead of at 25.0 s.
The seven are the contract, not a capability gain — but they are not nothing
either, because a killed run loses the model, the proof and the evidence it had
already produced, and an `unknown` at the budget keeps all three. Three of the
seven are the `32_1_cilled…` family the previous note left open.

**Two of the four "converts" were noise, and re-running is what found them.**
Re-run twice more in both arm orders on a quiet box, the two `QF_IDL` files
(`a9.8.11.asp`, `20.18.schur.lp`) are decided by the BEFORE arm too, in 6.8–10.9
s — their `unknown 25.03 s` in the sweep was the box at load ~100, not the
baseline's behaviour. The three `QF_UFLRA` converts reproduced on every run in
both orders:

| file | before | after | z3 | cvc5 | `:status` |
|---|---|---|---|---|---|
| `cpachecker-induction.minepump_spec2_product38…` | unknown 25.01 | **unsat 18.09** | unsat | unsat | unsat |
| `cpachecker-induction.minepump_spec2_product62…` | unknown 25.01 | **unsat 18.07** | unsat | unsat | unsat |
| `cpachecker-induction.minepump_spec3_product23…` | unknown 25.01 | **sat 6.31** | sat | sat | sat |

So: **raw 5 converts / 11 freed kills; re-checked 3 converts / 10 freed kills**,
all ten in `QF_UFLRA`. Every standing convert is confirmed three independent
ways. The cross-checker's exit status depends on the finding — a planted wrong
verdict on a known file makes it print `DISAGREE` and exit 1.

## The method this note is actually about

The 2026-09-12 pattern list said the check that finds these is "for each stretch
of work that can take seconds, name the poll that bounds it." That is right and
it is not enough, because it is a check you run against code you are already
reading, and the whole difficulty was that nobody was reading `dpll_lia`'s
abstractor. Two additions:

- **A profile answers a different question from a budget.** Cycles concentrate
  in the callee; budget is consumed by the caller that loops. When a kill is the
  symptom, read the phase stack first and the profile second.
- **When one defect is found in a struct, grep for the other struct with the
  same job.** `Abstractor` and `ArithAbstractor` are two Boolean abstractors
  with the same recursion and one memo between them. A fix that names a type
  rather than a shape leaves its twin in place.
