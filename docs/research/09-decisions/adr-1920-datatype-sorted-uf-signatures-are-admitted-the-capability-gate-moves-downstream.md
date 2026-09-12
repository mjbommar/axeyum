# ADR-1920: A datatype-sorted UF signature is admitted; the capability gate moves downstream, and lifting it alone would have shipped a crash

Status: accepted
Index-summary: `check_uf_param_sort` / `check_uf_result_sort` rejected `Sort::Datatype(_)` at declaration time, which made four SMT-LIB divisions — UFDT (4,569), UFDTLIRA (7,749), AUFDTLIRA (11,043), UFDTNIRA (4,424), **27,785 files** — refuse to parse. Measured on a stride-pinned UFDT 200 at 24 s / 8 GiB: **155 of 200 (77.5 %) died at that gate**, so the division's real capability was never observable. Lifting the arm ALONE is unsafe and the experiment says so rather than the reading: `(declare-fun p (Color) Bool) (assert (p o))` — the simplest query the divisions can produce — **aborted the process with a stack overflow**, because `check_auto_dispatch` diverts on the datatype SORT, `datatype_native` has no rewrite for `p(o)`, and the residual is handed back to the dispatcher, which routes it straight back in; the dispatcher also recomputes its deadline on every entry, so `config.timeout` cannot break the cycle. Decision: **admit datatype parameters and results**, and move the capability gate to `datatype_native`, which fails closed — one arm naming `Op::Apply`-with-a-datatype-argument, plus a general no-progress guard. The guard is **not** a fence around that arm: it fires on an array whose ELEMENT sort is a datatype, a shape with no uninterpreted function anywhere that parses on main today and aborted the pre-change binary — so this ADR also fixes a live crash that predates it. A stability check over the OTHER three divisions then found a THIRD instance of the same cycle that both guards missed, and its root cause is the general rule this ADR is really about: `Features::note_sort` recurses into an array's component sorts, so `(Array Int Color)` diverts the dispatcher, while the route's "is there datatype content" scan tested only `Sort::Datatype(_)` on the term — **when a dispatcher diverts on predicate A and the route decides "nothing to do" on predicate B, A and B are one predicate whether or not they are one function**, and `A ∧ ¬B` plus a call back into the dispatcher is a non-terminating loop by construction, invisible to a timeout that re-arms and to every soundness test because it presents as a crash. There is now one `sort_mentions_datatype`, at three call sites; mutation-verified (delete the array recursion and exactly one test dies, by name). Result on the pinned 200: parse 45/200 → **200/200**, decided 20/200 → **22/200**, **0 lost, 0 flips, 0 disagreements** against 19 declared `:status` values or against cvc5 1.3.4, and 0 aborts across 100 files spanning all four divisions. The decide rate barely moves, and that is the honest headline — what the lift actually buys is that **70.5 % of the division now names its blocker instead of failing to parse**: 80 files (40.0 %) on congruence over datatype UF arguments, 61 (30.5 %) on `is`/`select` over a datatype UF result. Sequences stay gated; no lane has measured them.
Date: 2026-09-12

## Context

Four SMT-LIB 2024 divisions are unmeasured, and the parity ledger has never
carried a row for any of them:

| division | files | in the ledger |
|---|---:|---|
| AUFDTLIRA | 11,043 | no |
| UFDTLIRA | 7,749 | no |
| UFDT | 4,569 | no |
| UFDTNIRA | 4,424 | no |
| **total** | **27,785** | |

Every one of them failed the same way, at parse:

```
term error: sort mismatch: expected Bool, BitVec, Float, Int, Real, array,
or uninterpreted sort, found (Datatype 0)
```

That comes from `crates/axeyum-ir/src/arena.rs`, `check_uf_param_sort` and
`check_uf_result_sort`, both of which rejected `Sort::Datatype(_)`. The doc
comment said datatype results "remain under their separate theory gates", so it
was a deliberate arm, not an oversight — which is why this ADR exists rather
than a one-line diff.

The premise was not obviously wrong. We *do* support quantifier-free datatypes:
`QF_DT` scored 114/200 against cvc5's 192 on 2026-09-11
(`bench-results/PARITY.md`). So datatypes exist in the IR and decide. The open
question was narrower: does a UF whose parameter or result is a datatype work
**end to end** — congruence, model lifting, evidence — or does the gate stand in
for machinery that genuinely is not there?

## What was measured

Everything below is on `s4`, release binaries, per file 24 s wall and 8 GiB
address space, against a benchmark list pinned and committed **before** a single
file was solved (`bench-results/parity-lists/UFDT.txt`, commit `49a0e2698`,
sha256 `113a9c93b6df…`, population 4,569, stride 22, 200 files). UFDT is the
smallest of the four and was chosen for that reason.

### 1. The gate's cost, before touching anything

| | files | share |
|---|---:|---:|
| rejected by the IR gate | 155 | 77.5 % |
| parsed | 45 | 22.5 % |
| **decided** (18 unsat + 2 sat) | **20** | **10.0 %** |
| unknown | 24 | 12.0 % |
| timeout | 1 | 0.5 % |

So the division's capability was not "low" — it was *unobservable*. Three
quarters of it never reached a solver.

### 2. Lifting the arm alone: the process aborts

The arm was lifted with nothing else changed, and seven shapes were run. Reading
the code predicted the result; running it is what settles it.

| shape | result |
|---|---|
| `declare-fun p (D) Bool` | admitted |
| `declare-fun f (Int) D` | admitted |
| `(assert (p o))` | **stack overflow, SIGABRT** |
| `(= x y) ∧ p(x) ∧ ¬p(y)` | **stack overflow, SIGABRT** |
| `p(red) ∧ p(green) ∧ ¬p(c)` | `Unsupported` |
| `p(red) ∧ ¬p(green)` | `Unsupported` |
| `is-mk(f 1)` | `Unsupported` |
| `select_v(f 1) = 5 ∧ select_v(f 1) = 6` | **`unsat`** — correct |
| `is-red(c) ∧ p(c) ∧ ¬p(red)` | `Unsupported` |

Nothing answered *wrongly*. But the two aborts are worse than an `unknown`: a
harness reads SIGABRT as a crash, not as a first-class result, and the
`Unsupported` verdicts are not a defect either — the fragment is entitled to
refuse.

The cycle:

1. `auto.rs` `check_auto_dispatch` diverts on `Features::has_datatype`, which
   `note_sort` sets from `Sort::Datatype(_)` — the **sort**, not a datatype
   operator. Every branch of that diversion returns; there is no fall-through
   to the UF/EUF routes.
2. `datatype_native`'s tag/field expansion rewrites `is` / `select` / `==`
   sites. It has no rewrite for `p(o)`, and `reject_stray_datatype_operands`
   waves a bare `TermNode::Symbol` through as an operand of *any* op — so `o`
   survives into the residual and `scan.dt_symbols` is empty.
3. The empty-`dt_symbols` branch hands that residual back to `solve`, which
   diverts on the datatype sort again, with the same input. Forever.
4. The timeout does not break it: `check_auto_dispatch` recomputes
   `dispatch_deadline = Instant::now() + config.timeout` on **every** entry, so
   the budget resets at each level.

### 3. The same cycle, with no uninterpreted function anywhere

Point 2 above is about a bare symbol operand, and `Op::Apply` is not the only op
that takes one. An array whose ELEMENT sort is a datatype reaches it too:

```smt2
(declare-datatypes ((Color 0)) (((red) (green))))
(declare-const a (Array Int Color)) (declare-const b (Array Int Color))
(declare-const o Color)
(assert (= a (store b 1 o))) (assert (not (= a b)))
```

That file parses on `main` today — no UF, no lifted gate needed — and aborted
the **pre-change** binary with the identical stack overflow. So the
non-termination is a live defect that predates this ADR and is not caused by it.
It is also what makes the general guard below a check that can fail rather than
a fence around a case the `Op::Apply` arm already catches.

### 4. After the change

| | before | after |
|---|---:|---:|
| parsed | 45 / 200 (22.5 %) | **200 / 200 (100 %)** |
| decided | 20 / 200 (10.0 %) | **22 / 200 (11.0 %)** |
| unsat / sat | 18 / 2 | 20 / 2 |
| unknown | 24 | 25 |
| `Unsupported` | 0 | 153 |
| newly decided | — | **2** (both `unsat`) |
| decided → undecided | — | **0** |
| `sat` ↔ `unsat` flips | — | **0** |

Soundness — **0 disagreements**, two independent checks:

| check | comparable | disagreements |
|---|---:|---:|
| declared `:status` in the benchmark file | 19 of 22 decided | **0** |
| cvc5 1.3.4, same list, same budget, same machine | 20 of 22 decided | **0** |

The two files cvc5 does not decide are the two we answer `sat`; both carry
`:status unknown`, and both were `sat` **before** this change as well — the
`sat` set is byte-identical before and after, so neither is introduced by it.
The two **newly** decided files are confirmed three ways: axeyum `unsat`, cvc5
`unsat`, declared `:status unsat`.

### 5. What the division is actually blocked on

This is the part worth having. With the gate lifted, every file reaches a route
and says why it stopped, so the division's blocker is now a census instead of a
guess:

| refusal | files | share |
|---|---:|---:|
| UF applied to a **datatype argument** | 80 | 40.0 % |
| `is`/`select` over a non-variable datatype term (a **datatype UF result**) | 61 | 30.5 % |
| e-matching round / time budget | 24 | 12.0 % |
| array or UF **datatype fields** | 12 | 6.0 % |
| quantified solve budget | 2 | 1.0 % |
| decided | 22 | 11.0 % |

**70.5 % of UFDT is blocked on one missing capability in two spellings**:
congruence over datatype-sorted uninterpreted-function terms. Before this change
that number could not be computed at all.

### 6. The predicate that had to be widened — found by checking the OTHER divisions

Measuring one division and shipping would have missed this. A stability
spot-check over the other three (25 stride-sampled files each, 10 s, asking only
*does anything abort*) found one that did: a 22 KB `AUFDTLIRA` benchmark that
still overflowed a **1 GiB** stack — an unbounded cycle, not a deep term — and
whose ring did not pass through either guard above.

The cause is one layer up:

> `Features::note_sort` **recurses into an array's component sorts**, so
> `(Array Int Color)` sets `has_datatype` and the dispatcher diverts. But
> `datatype_elim::first_datatype_term` and the §2 guard both asked
> `matches!(arena.sort_of(term), Sort::Datatype(_))` — and an array-of-datatypes
> TERM has sort `Array`. Divert says yes, content says no, the route hands the
> unchanged input back, and it comes straight back.

**Two predicates that must agree, written twice, in different words, with
nothing making them agree.** There is now one, `sort_mentions_datatype`; three
call sites needed it, and fixing only the first two left the crash exactly where
it was. Mutation-verified: delete the array recursion and **exactly one** test
dies, by name, with a SIGABRT — while the older array fixture survives, because
the narrow predicate already caught it. That is the difference between a second
copy and a test.

After the fix, 100 files across all four divisions: **0 aborts**.

**Generalisable rule, and the reason this is in the ADR rather than only in the
commit:** when a dispatcher diverts to a route on predicate *A* and the route
decides "nothing to do here" on predicate *B*, *A* and *B* are one predicate
whether or not they are one function. If `A ∧ ¬B` is reachable and the route's
no-op path calls back into the dispatcher, that is a non-terminating loop by
construction. It will not be caught by a timeout if the dispatcher re-arms its
deadline, and it presents as a crash rather than a wrong answer — which is why
no soundness test finds it.

## Decision

1. **`check_uf_param_sort` and `check_uf_result_sort` admit `Sort::Datatype(_)`.**
   The IR is a *typing* gate. A capability gate placed there cannot be precise —
   it rejects the whole file for a declaration the file may never use in a shape
   we cannot handle, and it rejected 155 of 200 UFDT files to protect against a
   fragment boundary that `datatype_native` already enforces.

2. **The capability gate lives in `datatype_native`, and fails closed**, in two
   layers:
   - a dedicated `Op::Apply`-with-a-datatype-argument arm, whose message names
     the actual missing capability rather than a sort list; and
   - a general termination guard: a residual that still carries a
     datatype-sorted term is never handed back to the dispatcher.

3. **Sequences stay rejected at declaration time.** No lane has measured them
   end to end, and this ADR's whole argument is that a gate should be lifted on
   a measurement, not on a symmetry. `gate_still_rejects_a_sequence_parameter`
   and `…_result` fail if someone widens that arm without one.

4. **This is not a decide-rate win and is not to be reported as one.** +2 files.
   What it buys is a division that is measurable and a blocker that is named.

## Consequences

### What is now possible

- The four DT divisions parse, so they can be measured, and `scripts/parity-run.sh`
  routes them to cvc5 — the datatype solver of record and the leader in every DT
  division — rather than falling through to a `z3` build that did not compete in
  SMT-COMP 2025.
- A live crash is fixed: any query carrying a datatype-sorted term that the
  expansion cannot eliminate now returns `Unsupported` instead of aborting. The
  array-of-datatypes shape above reached this on `main` with no UF at all.

### What is still refused, and what to build next

The next capability is stated precisely because §5 measured it: **Ackermann
congruence over expanded datatype arguments**, which addresses 40.0 % of the
division directly and is a prerequisite for the 30.5 % result-sort case.

The shape is already half-built — `build_dt_eq` compares tag plus scalar fields,
which is **exact** for a datatype with no datatype-typed field. So for each
uninterpreted function whose datatype arguments are over such datatypes, replace
each application with a fresh symbol of the result sort and add, for each pair of
applications, `(conjunction of per-argument equalities) → (results equal)`.

**The soundness condition is not optional and is the reason this ADR does not
just do it.** For a datatype that *does* have datatype-typed fields,
`build_dt_eq` is a **relaxation** — weaker than real equality — and a weaker
antecedent makes the congruence constraint *stronger* than the true axiom, which
can produce a wrong `unsat`. So the slice must be restricted to datatypes with
scalar fields only, and the restriction has to be a checked precondition rather
than a comment.

### What this ADR does not claim

- It does not claim UF-over-datatypes *works*. It claims the declaration is
  admissible, every reachable shape either decides correctly or refuses, and the
  refusals are now precise enough to prioritise.
- The decide rates in §4 were taken on a shared, loaded dev box. The **parse**
  rate is load-independent and is the number this ADR rests on; the two
  newly-decided files are a per-file diff against the same list, not a
  difference of two aggregates.
- One `--lib` sweep run concurrently with this lane's measurement reported
  `check_qf_uf_with_config_is_bounded_by_timeout` FAILED. Re-run alone it passes
  in 527 s against its own 600 s budget — it is a contention artifact of a
  timing assertion, and it touches neither datatypes nor UF signatures.
- **No `PARITY.md` row was produced.** `scripts/parity-run.sh UFDT` aborts with
  "the reference decided 0 of 5 probe benchmarks". The invocation is not wrong —
  it passes the same `--tlimit=24000` under which cvc5 decided 20 of our 22 —
  cvc5 simply decides none of the *first five* files of this list at 24 s, so
  the guard's premise does not hold in UFDT. `PARITY_ALLOW_WEAK_REFERENCE=1`
  does not apply: its own text says "only if the reference really is beaten by
  all 5", and it is not. Overriding a safety guard to manufacture a ledger row
  is the failure the ledger exists to prevent, so there is no row and the
  measurement note carries the numbers.
- The brief that opened this lane named the fourth division `AUFDTNIRA`; the
  4,424-file division is `UFDTNIRA` (`AUFDTNIRA` is a different, smaller one at
  1,567). The **total is right** — 11,043 + 7,749 + 4,569 + 4,424 = 27,785 — and
  that is what identifies which was meant. These four are also not all of it:
  every `*DT*` non-incremental division sums to 44,690 files, and the UF-bearing
  ones beyond these four hit the same gate. The four are the claim because they
  are the four that were measured.

## Evidence

- `crates/axeyum-solver/tests/dt_uf_gate.rs` — 9 tests. The `sound_*` ones
  assert the **absence of the wrong answer** rather than the presence of the
  right one, because the fragment is entitled to refuse; one positive control
  (`sound_congruence_through_a_datatype_result_is_unsat`) actually decides, so
  the file cannot be satisfied by a route that refuses everything. The
  `terminates_*` ones are the two measured aborts.
- `docs/research/03-measurements/uf-over-datatypes-2026-09-12.md` — the run
  protocol, the per-file diff and the refusal census.
- `bench-results/parity-lists/UFDT.txt` — the pinned list, committed before the
  measurement.
