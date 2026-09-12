# What happens when an uninterpreted function takes or returns a datatype

Measured 2026-09-11/12 on `s4`, release binaries, 24 s wall and 8 GiB address
space per file. Lane `dt-uf`. The decision this note supports is
[ADR-1920](../09-decisions/adr-1920-datatype-sorted-uf-signatures-are-admitted-the-capability-gate-moves-downstream.md).

**The answer in one line: the machinery is sound but incomplete, the gate that
hid that was in the wrong layer, and lifting it alone would have shipped a
process abort on the simplest query the affected divisions can produce.**

**Verdict: BUILD** — admit the signature, move the capability gate into
`datatype_native`, and fail closed there. **Do NOT** report it as a decide-rate
win: it is +2 files on 200. What it buys is that the division became
*measurable*, and that 70.5 % of it now names its blocker.

## The population, pinned before anything was run

`bench-results/parity-lists/UFDT.txt`, committed at `49a0e2698` **before a single
file was solved**, by the standard recipe:

```sh
LC_ALL=C find <div> -name '*.smt2' | LC_ALL=C sort | awk 'NR%22==1' | head -200
```

population 4,569 · stride 22 · 200 files · sha256 `113a9c93b6dfd9bd…`

UFDT is the smallest of the four divisions the gate blocked (UFDT 4,569,
UFDTLIRA 7,749, AUFDTLIRA 11,043, AUFDTNIRA 4,424 — **27,785 files**), which is
why it was measured first.

Verdicts were read with `target/release/examples/uf_unknown_probe`, which
surfaces the `SolverError` / `UnknownReason` that `smtcomp_cli` flattens to a
bare `unknown` — a parse failure and an incomplete search are both `unknown` at
the competition front door, and this measurement is entirely about telling them
apart.

## 1. Before: three quarters of the division never reached a solver

| | files | share |
|---|---:|---:|
| rejected by the IR gate (`sort mismatch … found (Datatype 0)`) | 155 | 77.5 % |
| parsed | 45 | 22.5 % |
| **decided** (18 `unsat` + 2 `sat`) | **20** | **10.0 %** |
| `unknown` | 24 | 12.0 % |
| timeout | 1 | 0.5 % |

## 2. Lifting the gate alone: two of nine shapes abort the process

The arm in `check_uf_param_sort` / `check_uf_result_sort` was lifted with nothing
else changed, and nine shapes were built directly against the arena. Reading the
code predicts these; running them is what settles it.

| shape | result |
|---|---|
| `declare-fun p (D) Bool` | admitted |
| `declare-fun f (Int) D` | admitted |
| `(assert (p o))` | **stack overflow, SIGABRT (rc 134)** |
| `(= x y) ∧ p(x) ∧ ¬p(y)` | **stack overflow, SIGABRT (rc 134)** |
| `p(red) ∧ p(green) ∧ ¬p(c)` | `Unsupported` |
| `p(red) ∧ ¬p(green)` | `Unsupported` |
| `is-mk(f 1)` | `Unsupported` |
| `select_v(f 1) = 5 ∧ select_v(f 1) = 6` | **`unsat`** — correct |
| `is-red(c) ∧ p(c) ∧ ¬p(red)` | `Unsupported` |

Nothing answered *wrongly*, which is the important half. But an abort is worse
than an `unknown`: a harness reads it as a crash, not as a first-class result.

**The cycle.** `auto.rs::check_auto_dispatch` diverts on `Features::has_datatype`,
which `note_sort` sets from the **sort** `Sort::Datatype(_)`, not from a datatype
operator — and every branch of that diversion returns. `datatype_native`'s
tag/field expansion rewrites `is` / `select` / `==` sites and has no rewrite for
`p(o)`; `reject_stray_datatype_operands` waves a bare `TermNode::Symbol` through
as an operand of *any* op, so `o` survives into the residual and
`scan.dt_symbols` is empty. The empty-`dt_symbols` branch then hands that
residual back to `solve`, which diverts on the same sort, with the same input.
Forever. The timeout does not break it either: `check_auto_dispatch` recomputes
`dispatch_deadline = Instant::now() + config.timeout` on **every** entry, so the
budget resets at each level of the recursion.

## 3. The same cycle with no uninterpreted function anywhere

`reject_stray_datatype_operands` waving a bare symbol through is not specific to
`Op::Apply`. An array whose ELEMENT sort is a datatype reaches it too:

```smt2
(declare-datatypes ((Color 0)) (((red) (green))))
(declare-const a (Array Int Color)) (declare-const b (Array Int Color))
(declare-const o Color)
(assert (= a (store b 1 o))) (assert (not (= a b)))
```

This file parses on `main` today — no UF, no lifted gate required — and aborted
the **pre-change** binary with the identical stack overflow:

```
thread 'main' has overflowed its stack
fatal runtime error: stack overflow, aborting   [rc=134]
```

So the non-termination is a **live defect that predates the gate lift**. It is
also why the general termination guard added in ADR-1920 is a check that can
fail rather than a fence around a case the `Op::Apply` arm already catches — a
guard whose only reachable trigger is already handled by the arm above it would
be exactly the un-failable checker this repository keeps finding.

## 4. After: the division is measurable

| | before | after |
|---|---:|---:|
| parsed | 45 / 200 (22.5 %) | **200 / 200 (100 %)** |
| decided | 20 / 200 (10.0 %) | **22 / 200 (11.0 %)** |
| `unsat` / `sat` | 18 / 2 | 20 / 2 |
| `unknown` | 24 | 25 |
| `Unsupported` | 0 | 153 |

Per file, not as a difference of aggregates:

* **newly decided: 2**, both `unsat`
* **decided → undecided: 0**
* **`sat` ↔ `unsat` flips: 0**
* the `sat` set is **byte-identical** before and after — neither `sat` verdict is
  introduced by this change

## 5. Soundness: zero disagreements, two independent checks

| check | comparable | disagreements |
|---|---:|---:|
| declared `:status` in the benchmark file | 19 of 22 decided | **0** |
| cvc5 1.3.4 (`git f3b21c4`), same list, same budget, same machine | 20 of 22 decided | **0** |

The two files cvc5 does not decide are the two we answer `sat`; both carry
`:status unknown`, both were `sat` **before** this change as well, so they are
not evidence for or against it. The two **newly** decided files are confirmed
three ways — axeyum `unsat`, cvc5 `unsat`, declared `:status unsat`.

(The three files where cvc5 returns `none_rc134` are aborts under the protocol's
8 GiB address-space cap. Per the parity protocol they count as not solved.)

## 6. What the division is actually blocked on

This is the part worth having, and it could not be computed at all before: every
file now reaches a route and says why it stopped.

| refusal | files | share |
|---|---:|---:|
| UF applied to a **datatype argument** | 80 | 40.0 % |
| `is`/`select` over a non-variable datatype term (a **datatype UF result**) | 61 | 30.5 % |
| e-matching round / time budget | 24 | 12.0 % |
| array or UF **datatype fields** | 12 | 6.0 % |
| quantified solve budget | 2 | 1.0 % |
| decided | 22 | 11.0 % |

**70.5 % of UFDT is one missing capability in two spellings**: congruence over
datatype-sorted uninterpreted-function terms.

## Recommendation

**BUILD (landed):** admit the signature; gate downstream; fail closed. This also
fixes the §3 crash.

**BUILD NEXT, with a checked precondition:** Ackermann congruence over expanded
datatype arguments — 40.0 % of the division directly, and a prerequisite for the
30.5 % result-sort case. Half of it exists: `build_dt_eq` compares tag plus
scalar fields. Replace each application with a fresh symbol of the result sort
and add, per pair of applications, `(conjunction of per-argument equalities) →
(results equal)`.

**The precondition is not optional.** For a datatype that has datatype-typed
fields, `build_dt_eq` is a **relaxation** — weaker than real equality — and a
weaker antecedent makes the congruence constraint *stronger* than the true
axiom, which can produce a wrong `unsat`. The slice must be restricted to
datatypes whose fields are all scalar, and that restriction has to be a checked
precondition in the scan, not a comment.

**DO NOT BUILD:** more budget. 12 % of the division is on an e-matching or
quantifier budget and 70.5 % is on a missing capability; raising the clock moves
the smaller number.

## Caveats

* `s4` is shared and was loaded throughout (load average 10–15, several lanes
  building). The **parse** rate is load-independent and is what the decision
  rests on. The decide-rate delta is a per-file diff against one pinned list, not
  a difference of two aggregates, so a file that merely timed out differently
  cannot appear as a gain.
* One concurrent `--lib --features full` sweep reported
  `check_qf_uf_with_config_is_bounded_by_timeout` FAILED. Re-run alone it passes
  in 527 s against its own 600 s budget — a contention artifact of a wall-clock
  assertion, touching neither datatypes nor UF signatures.
* Reproduction: `crates/axeyum-solver/tests/dt_uf_gate.rs` carries all nine
  shapes from §2 and §3 as committed tests. For a file, use
  `target/release/examples/uf_unknown_probe <file.smt2> <timeout_ms>`.
