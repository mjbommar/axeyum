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
UFDTLIRA 7,749, AUFDTLIRA 11,043, UFDTNIRA 4,424 — **27,785 files**), which is
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

## 7. A THIRD instance of the same cycle, found by checking the other divisions

Measuring one division and shipping would have missed this. A stability
spot-check — 25 stride-sampled files from each of the other three divisions, at
10 s, asking only *does anything abort* — found one that did:

`AUFDTLIRA/20200306-Kanig/spark2014bench/P518-021__frame_for_max__…`, 22 KB,
still overflowing a **1 GiB** stack. An unbounded cycle, not a deep term.

`gdb` gave the ring, and it did not pass through the two guards already in
place. The root cause is one layer up from §2:

> `Features::note_sort` **recurses into an array's index and element sorts**, so
> `(Array Int Color)` sets `has_datatype` and the dispatcher diverts. But
> `datatype_elim::first_datatype_term` and the §2 guard both asked
> `matches!(arena.sort_of(term), Sort::Datatype(_))`, and an array-of-datatypes
> TERM has sort `Array`. Divert says yes, content says no, the route hands the
> unchanged input back to `solve`, and `solve` sends it back.

**Two predicates that have to agree, written twice, in different words.** There
is now one, `sort_mentions_datatype`, and three call sites needed it — found one
at a time by rebuilding and re-running the file, not by reading:

1. `datatype_elim`'s fall-through `solve`;
2. `datatype_native`'s post-expansion `solve` — *not* redundant with the
   `dt_symbols.is_empty()` guard, because `replacements` only covers the
   `is`/`select`/`==` sites the scan collected, so a datatype symbol reached only
   through an array `store` survives into `reduced` even when `dt_symbols` is
   **non**-empty;
3. the guard's own predicate, which was still the narrow one — fixing 1 and 2
   with the narrow predicate left the crash exactly where it was.

**Mutation-verified.** Delete the array recursion from `sort_mentions_datatype`
and **exactly one** test dies, by name and loudly:

```
test terminates_on_an_array_of_datatypes_with_no_datatype_sorted_term
thread '…' has overflowed its stack / SIGABRT
```

The older `terminates_on_an_array_of_datatypes` **survives** that mutation — it
carries a datatype-sorted `o` inside a `store`, which the narrow predicate
already caught. That is what makes the new fixture a test rather than a second
copy of the old one; it asserts inside the test body that no term has sort
`Datatype`.

Re-run after the fix, all four divisions, 100 files:

| division | sampled | aborts |
|---|---:|---:|
| UFDTLIRA | 25 | 0 |
| AUFDTLIRA | 25 | **0** (was 1) |
| AUFDTNIRA | 25 | 0 |
| UFDTNIRA | 25 | 0 |

## 8. Two things this lane got wrong on the way in

**The fourth division was misnamed in the brief.** Counted here:

| division | files |
|---|---:|
| AUFDTLIRA | 11,043 |
| UFDTLIRA | 7,749 |
| UFDT | 4,569 |
| **UFDTNIRA** | **4,424** |
| total | **27,785** |

`AUFDTNIRA` is a different, smaller division (1,567). The **total is right** —
11,043 + 7,749 + 4,569 + 4,424 = 27,785 — which is what identifies `UFDTNIRA` as
the one meant. These four are not the whole of it either: every `*DT*`
non-incremental division sums to **44,690** files, and the UF-bearing ones beyond
these four (AUFBVDTLIA 1,683, AUFBVDTNIRA 2,125, UFFPDTNIRA 795, AUFDTLIA 795,
UFDTLIA 328, …) hit the same gate. The four are the claim because they are the
four that were measured.

**No `PARITY.md` row was produced, and the reason is a real finding.**
`scripts/parity-run.sh UFDT` aborts before scoring:

```
FAIL: the reference decided 0 of 5 probe benchmarks.
      A crippled reference reads as a win for us, so this ABORTS.
```

The invocation is not wrong — the script passes `--tlimit=24000`, identical to
the hand run in §5 where cvc5 decided 20 of 22 — cvc5 simply does not decide any
of the **first five** files of the stride-pinned list at 24 s. The guard's
premise (a division's leading reference decides at least one of any five files)
does not hold in UFDT. `PARITY_ALLOW_WEAK_REFERENCE=1` exists, but its own
documentation says to set it "only if the reference really is beaten by all 5",
and it is not — we do not decide those five either. **Overriding a safety guard
to manufacture a ledger row is the failure mode the ledger exists to prevent**,
so the row was not produced and this note carries the numbers instead. The
`parity-run.sh` change that routes the DT divisions to cvc5 rather than to a
`z3` build that did not compete in SMT-COMP 2025 is kept: the fall-through it
replaces is strictly worse, whether or not this division can be scored today.

## 9. Re-measured after the §7 fix, and a QF_DT control

The §4–§6 numbers were taken before §7's predicate widening, so the whole
200-file sweep was re-run on the final binary. **Identical**: 22 decided (20
`unsat` + 2 `sat`), the same 2 newly decided, 0 lost, 0 flips, and the same
refusal census (80 / 61 / 12). The decided SET is byte-identical to the one
cross-checked against cvc5 in §5, so that differential still applies verbatim.

The one difference is a resource artifact, not a verdict: the list's heaviest
file (`abstract_completeness/x2015_09_10_16_59_33_621_1039748`) hit the
protocol's 8 GiB cap — `memory allocation of 411181056 bytes failed` — where it
had returned `unknown` in both earlier sweeps at the same ~25 s. It is on the
edge of the memory ceiling and the loaded box pushed it over; it counts as not
solved either way.

**QF_DT control.** Widening a predicate makes MORE queries route into the
datatype theory, so the thing to rule out is that it costs capability where
datatypes already worked. 60 files from the committed `QF_DT` parity list, the
**pre-change binary and the final binary alternating per file** so a load drift
hits both arms equally:

| | unsat | sat | unknown | refused |
|---|---:|---:|---:|---:|
| pre-change | 28 | 10 | 5 | 17 |
| final | 28 | 10 | 5 | 17 |

**0 of 60 files differ.**

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
