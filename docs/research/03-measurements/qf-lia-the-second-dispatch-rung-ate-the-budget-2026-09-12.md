# QF_LIA: the second dispatch rung ate the budget on 23 of 55 gap files

**2026-09-12, lane `QF-LIA-GAP`.** The first census of `QF_LIA`'s addressable
gap — all 55 winnable files of the 2026-09-11 board, not a sample. Raw rows and
method: [`bench-results/qf-lia-gap-census-20260912/`](../../../bench-results/qf-lia-gap-census-20260912/README.md).

**In one line: 30 of the 55 files never ran the dispatch ladder at all, because
`term_identity::identity_normal_form` — the SECOND rung of `check_auto`, with no
deadline and no route attempt of its own — is an exponential tree walk over a
shared `ite` DAG, and it was consuming the whole 24 s budget before any solver
route was reached.**

## 1. What the board says, re-derived

| | files of 200 |
|---|---:|
| axeyum | 119 |
| z3 4.13.3 | 172 |
| cvc5 1.3.4 | 139 |
| best-of-reference | **174** |
| we decide, neither reference does | **0** |

So the addressable gap is **55** against best-of-reference, 53 against z3 alone
and 22 against cvc5 alone. Name the reference when quoting it.

## 2. The census measured the ladder on 30 of 55 files

A completed `QF_LIA` dispatch records `attempts=16` in `--trace`.

| `attempts=` | files |
|---|---:|
| none (no trail published at all) | 1 |
| **2** | **23** |
| 3–5 | 5 |
| 13–16 | 26 |

`attempts=2` is `fd:parse`, `probe`, and then nothing for 24.9 s. The phase
breadcrumb (`8860e2a60`) reads `stack=none depth=0 in=none` on every one of
those 23, and `route-open` says `ms=24939 after=probe`: the worker was outside
every instrumented frame for the entire budget.

This is [ADR-1927](../09-decisions/adr-1927-a-ladder-rungs-fragment-refusal-is-a-decline-not-the-querys-verdict.md)'s
shape with the polarity changed. There, a rung *refused* early and its refusal
became the file's answer. Here a rung *hangs* early, and the watchdog kill
becomes the file's answer. Both produce a census that is reproducible, stable
across samples, and a description of the dispatcher rather than of the queries.

**The check that catches both is the same one: `attempts=` against the ladder
length, before ranking any reason.**

## 3. The phase, named by three instruments in sequence

1. **The route trail** put 24.9 s of a 25.0 s run in the unattributed open
   segment, `after=probe`. `record_probe` is the last thing `check_auto` does
   before its first real rung, so the phase is between the probe and
   `term-identity-refuter`'s own (never reached) record site.
2. **The phase breadcrumb** said `stack=none`. That is a positive finding, not
   a missing reading: the worker was in code with no frame, which rules out
   every `lra`, `lia`, `dpll`, `euf`, `dl` and `simplex` phase — all of which
   carry one.
3. **A `perf` leaf profile** named it. Three files, three different `nec-smt`
   directories, one symbol:

   | file | share of run |
   |---|---:|
   | `checkpass_pwd/prp-17-34.smt2` | **99.81 %** |
   | `getoption_directories/prp-9-46.smt2` | **97.43 %** |
   | `getoption/prp-2-200.smt2` | **95.38 %** |

   `axeyum_solver::term_identity::identity_normal_form`, every time. A leaf
   profile needs no unwinder, which is why it works here where a DWARF
   call-graph on the same binary produces no usable Rust caller frames.

## 4. The defect

```rust
fn identity_normal_form(arena: &TermArena, term: TermId) -> (TermId, bool) {
    // … non-constant condition:
    let (then_norm, then_changed) = identity_normal_form(arena, *then_term);
    let (else_norm, else_changed) = identity_normal_form(arena, *else_term);
```

Both branches, native recursion, **no memo**. Assertions are a shared DAG — an
SMT-LIB `let` makes one `ite` reachable from many parents — so the walk is
exponential in the nesting depth rather than linear in the DAG. The `nec-smt`
`prp-*` family is one `(assert (let … (let … )))` carrying 519–11,162 `ite`
terms over 25–372 integer variables, which is exactly that shape.

Three properties compound it, and each is separately worth noticing:

- **It is the second rung.** `check_auto` runs `wide_int_decline`, then
  `term_identity_refutation`, then everything else. Nothing downstream can
  rescue a query that does not leave rung 2.
- **It takes no deadline.** Not a stride whose counter is too coarse for the
  work, and not a `None` argument passed to a function that polls — this phase
  reads no clock at all, so the budget is enforced only by killing the process.
- **It records no route attempt.** A route that declines leaves a trail entry;
  a route that never returns leaves nothing. That is why every instrument in
  the tree agreed the file had done almost no work.

This is now the **fourth** instance of "a phase the budget cannot see"
(see [`watchdog-kills-are-a-deadline-blind-phase-2026-09-12.md`](watchdog-kills-are-a-deadline-blind-phase-2026-09-12.md)),
and the **second** where the mechanism is specifically *a tree walk over a DAG
with no memo*. The first was `dpll_t::Abstractor::abstract_term` (`c4046c2d6`).

## 5. The fix

Memoise, and make the walk iterative. The memo is denotation-identical —
`identity_normal_form` is a pure function of the term, and unlike `affine_in`
and `interval_of` nearby it carries **no depth cap**, so there is no
order-dependent widening to reason about: the table only removes repeated
derivations of the same answer. Iterative rather than recursive because the
nesting depth is the *source's*, and a stack overflow aborts the process
instead of yielding a first-class `unknown`.

The unit test that pins it fails by not finishing rather than by asserting: 64
levels of `ite(c, t, t)` is `2^64` derivations over a 64-node DAG. It is also a
value assertion — the chain normalises to `x` and the disequality is refuted —
and it carries a non-vacuity check that the arena did not fold the chain away at
construction. A companion test builds the same shape with branches that
genuinely differ and requires that it is **not** refuted, so a memo that
manufactured a refutation would be caught.

## 6. What the fix is and is not worth

Interleaved per-file A/B over the **whole 200-file division** — both arms of one
file back to back on the same pinned P-core pair, arm order alternating per file
(100 `A-first`, 100 `B-first`), 24 s budget, 120 s wrapper, two workers on
disjoint halves and disjoint core pairs.

| | base | fixed |
|---|---:|---:|
| decided | 116 | **117** |
| gains (undecided → decided) | — | **1** |
| losses (decided → undecided) | — | **0** |
| `sat` ↔ `unsat` flips | — | **0** |
| rows with no verdict at all | — | **0** |
| total wall | 2119.9 s | **2030.7 s** (**−4.2 %**) |

**One convert**, and it is checked four ways:

| `nec-smt/small/print_file/prp-0-47.smt2` | |
|---|---|
| base | `unknown`, 25.02 s (watchdog kill) |
| fixed | **`sat`, 0.51 s**, decided by `dl-online` |
| re-run in isolation | base `unknown`, fixed `sat` — the pairing reproduces |
| z3 4.13.3 `-T:24` | `sat` |
| cvc5 1.3.4 `--tlimit 24000` | `sat` |
| declared `(set-info :status …)` | `sat` |

**One convert out of 23 files whose whole budget this phase was eating.** That
is the honest headline, and it is consistent with the board-wide record: 149
watchdog kills have so far yielded 2 converts in `QF_UFLRA` and 1 here. A
census of a failure mode is not a count of fixable files.

What the fix *is* worth is two things the convert count does not show:

- **21 of the 23 now return a first-class `unknown` with a reason** instead of
  being killed. A killed worker loses the verdict, the model and any evidence it
  produced, and — as §2 shows — makes the division's census a description of the
  dispatcher. §7 is a fact about `QF_LIA` that could not be stated before.
- **−4.2 % wall over the division at zero verdict cost**, because a query that
  used to burn 25 s in rung 2 now reaches a route that gives up in 10–22 s.

Three caveats on the numbers, stated rather than smoothed:

- The A/B baseline decides **116**, not the board's 119. The three missing are
  `ex3000_2400_100`, `ex4320_2400_100` and `ex6960_2400_100`, and all three are
  `unknown` in **both** arms at 24.1–24.3 s: the box carried two other lanes'
  sweeps during this run, and those files sit against the budget. The effect is
  symmetric and cannot favour either arm.
- The single convert was **re-run in isolation** before being reported, because
  a 25 s-vs-0.5 s pairing at a 24 s budget is exactly the shape that a load
  spike manufactures. It reproduced.
- Wall is a sum over 200 files; it is dominated by the 23 that stop earlier, not
  by a general speedup. Nothing here claims the solver got faster.

## 7. What the corrected census says the division actually needs

Same 55 files, same protocol, same binary except the memo. Full table in the
[census README](../../../bench-results/qf-lia-gap-census-20260912/README.md).

| cause | base | corrected |
|---|---:|---:|
| un-instrumented phase right after `probe` | **23** | **0** |
| `lia-dpll` pre-SAT skeleton admission boundary | 4 | **23** |
| lazy LIA CDCL(T) rounds out of clock | 7 | 9 |
| LIA branch-and-bound out of clock | 6 | 6 |
| LIA `sat`-model reconstruction out of clock | 5 | 5 |
| `i128` boundary in the exact-rational simplex | 3 | 3 |
| other watchdog phases | 5 | 6 |
| INGEST (parse is outside `--timeout-ms`) | 1 | 2 |
| **decided** | 0 | **1** |

Files reaching `attempts` 13–16: **26 before, 48 after**.

The obvious next lever is then the admission boundary that 20 of the 23 land on.
Three measurements on `prp-17-34.smt2` say **DO NOT BUILD IT**, and none of them
required shipping anything:

| lever | measurement | result |
|---|---|---|
| lift the envelope | `MAX_MODERATE_PRE_SAT_ARITH_ATOMS`/`..._CNF_VARS` set to a million (probe binary only, reverted), 24 s | `unknown` — a different `ResourceLimit`, now inside the lazy LIA loop |
| lift it **and** spend 2.5× the clock | same, **60 s** | `unknown`, same shape |
| bypass admission entirely | `check_qf_lia_online_cdclt` called directly on the parsed assertions with the whole budget — what `oversized_admission_probe` would run | **declines in 6 ms**: *"online CDCL(T) LIA model did not replay (arithmetic outside the …)"* |

The third row is the one that settles it. The route the admission gate is
holding back cannot decide these queries **at any budget**: its atom
abstraction (`lia_online::is_lia_atom`) accepts `(= x (ite c a b))` as one
opaque integer equality atom, so the driver returns `Sat` on a skeleton whose
model then fails `replays_integer` against the originals
(`lia_theory.rs:238`). So the 27-file
`prp-*` family is a **capability** gap, not a budget gap and not an
admission-constant gap.

That is the finding the base census could not have produced, because on 23 of
those 27 files the base census's answer was the name of the rung that hung.
This also repeats `QF_LRA`'s and `QF_NIA`'s closed hypotheses in a third
division: **more clock buys nothing here either.**

## 8. A second instance of the same defect, named and not fixed

`RC-09` and `RC-11` spend their whole budget with `stack=none` immediately after
`cas-int-units`, and a `perf` leaf profile puts **81.66 %** of `RC-09` in
`auto::affine_in`, reached from `auto::prove_int_box` — a recursive walk over
the same shared DAG with no memo, on a rung that also takes no deadline. Its
neighbours `interval_of` and `accumulate_max_abs` have the same shape.

**Not fixed here, deliberately.** Unlike `identity_normal_form`, `affine_in`
carries a depth cap (`depth > 256 → None`), so a memo keyed on the term returns
an answer computed at whatever depth the node was *first* reached and would let
`prove_int_box` prove a box for queries it previously declined. That is a
capability widening, sound but not free, and it needs its own A/B rather than
being smuggled in behind a performance fix. The conservative alternative —
give `decide_bounded_int_box_by_evaluation` a deadline, so it declines instead
of eating the budget — is the smaller change and is what a follow-up should
price first.
