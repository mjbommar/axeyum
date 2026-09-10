# Category A: the universals with no trigger at all

**Date:** 2026-09-10
**Lane:** Q1-triggers
**Follows:** [`why-the-instantiation-loop-produces-nothing-2026-09-10.md`](why-the-instantiation-loop-produces-nothing-2026-09-10.md),
whose category A is 919 of 19,975 universal-**rounds** (4.6%) with `patterns=0`.
**Population:** the 32 files of `bench-results/parity-losses-20260908/UF.txt`.
**Method:** `AXEYUM_QPROBE=1 target/release/examples/axeyum_cli <file> --timeout-ms 24000`,
four at a time; the per-round rows
`universal[i] vars=… patterns=… joined=… starved_joins=… admitted=…` and the
matcher's own `egraph-fixpoint … foralls=… triggerless=…` field.

## 1. How many distinct universals, on how many files

A round-count cannot answer this: a triggerless universal reappears in every
round, so 919 rows could be 8 universals or 900. Read the matcher's own
`triggerless` field instead — it counts `CompiledUniversal`s with
`pattern_indices.is_empty() && !vars.is_empty()`, once per matcher build.

**535 distinct triggerless universals, on 17 of the 32 files.**

| | value |
|---|---:|
| distinct triggerless universals (sum of per-file `triggerless`) | **535** |
| files carrying at least one | **17 of 32** |
| universals compiled across the slice | 8,302 |
| triggerless share of compiled universals | **6.4%** |
| rows with `patterns=0` **and** `vars=0` (would not be category A) | **0** |

So the item is not "8 universals on 2 files". It is a per-file population that
reaches 101 on one file, and it is concentrated:

| file | universals | triggerless | bound-variable widths seen |
|---|---:|---:|---|
| f11 | 484 | **101** | 1–6 |
| f05 | 484 | **98** | 1–7 |
| f12 | 436 | **79** | 1–8 |
| f10 | 420 | 58 | 1–7 |
| f18 | 510 | 58 | 1–7 |
| f13 | 407 | 53 | 1–7 |
| f06 | 438 | 23 | 1–6 |
| f20 | 525 | 14 | 1–3 |
| f28 | 90 | 10 | 1–6 |
| f19 | 470 | 8 | 2–3 |
| f01 | 443 | 7 | 1–4 |
| f09 | 254 | 7 | 1–6 |
| f23 | 426 | 6 | 1–3 |
| f03 | 381 | 4 | 1–3 |
| f26 | 401 | 4 | 1–2 |
| f21 | 153 | 3 | 3 |
| f31 | 4 | **2 of 4** | 7, 11 |
| 15 other files | — | 0 | — |

**The refutation for this table:** if the `triggerless` field counted something
other than "compiled with no pattern", or if the same universal were counted
once per matcher rebuild, these numbers would be inflated. The field is read at
the fixpoint print from `matcher.quantifiers`, one entry per compiled universal,
and this table takes the **maximum** over rounds per file rather than the sum,
so a rebuild cannot double-count. The independent cross-check is `A_rows`
divided by fixpoint rounds per file, which agrees to within the three files that
build the matcher twice (f03, f21, f28).

Row counts differ from the source note's — 9,783 per-universal rows here against
19,975 there — because the box was not equally quiet and fewer fixpoint rounds
completed inside the same 24 s. That moves the round counts and leaves the
distinct counts alone, which is the reason to read the distinct count.

## 2. Why trigger selection returns nothing

`select_triggers` (`qinst_egraph.rs:7218`) is **not** limited to single
patterns — it already builds multi-patterns by greedy set cover, and the
`patterns=2` / `patterns=3` rows in the probe are that cover firing. It returns
empty in exactly one situation:

```rust
_ => return Vec::new(), // some variable is in no function application
```

Candidates come from `collect_app_candidates`, which keeps a subterm only when
its operator is `Op::Apply(_)` — an uninterpreted function or predicate
application — and which refuses to descend into a nested binder. So a bound
variable that occurs **only** under interpreted operators (`=`, the boolean
connectives, `ite`) is coverable by nothing, and the greedy cover then discards
the entire trigger, including every variable it had already covered.

`f31` is the whole mechanism on one page of SMT-LIB
(`UF/sledgehammer/TypeSafe/smtlib.1098821.smt2`, `:status unsat`, z3 refutes it
in 0.02 s with 4 instantiations). Its four universals are:

```
universal[0] vars=8  patterns=1 joined=44537 starved_joins=0 admitted=419
universal[1] vars=11 patterns=0 joined=0     starved_joins=0 admitted=0
universal[2] vars=7  patterns=0 joined=0     starved_joins=0 admitted=0
universal[3] vars=3  patterns=2 joined=2937  starved_joins=0 admitted=0
```

`universal[1]` is the file's nested `forall ((?v8 S6) (?v9 S7) (?v10 S7))`,
compiled by `collect_nested_registrations_rec` with the enclosing prefix it
uses — 8 outer variables plus its own 3, hence `vars=11`. Its body is

```smt
(=> (= ?v7 f9)
  (=> (= (f3 ?v0 ?v1 ?v2 ?v3 (f10 f11 ?v8)) f1)
    (=> (= (f12 ?v0 ?v8 ?v4 ?v9 ?v5) f1)
      (=> (= (f3 ?v0 ?v1 ?v2 ?v6 ?v10) f1)
        (=> (= (f13 ?v0 ?v10 ?v9) f1) false)))))
```

The application candidates cover `?v0 ?v1 ?v2 ?v3 ?v4 ?v5 ?v6 ?v8 ?v9 ?v10` —
**ten of the eleven**. `?v7` occurs exactly once, as `(= ?v7 f9)`, which is
`Op::Eq` and therefore not a candidate. One uncoverable variable out of eleven
throws away a cover that was otherwise complete. `universal[2]` is the same
defect on the file's other nested binder: 7 variables, `?v7` again reachable
only through `(= ?v7 f9)`.

This also explains the width correlation the coordinator noticed — the two
widest universals are the triggerless ones — without the width being the cause.
Width is not a threshold; it is more chances to contain one uncoverable
variable.

**The refutation for this claim:** if the cause were "no single term covers all
N variables", `select_triggers` would still return the greedy multi-pattern and
`patterns` would be ≥ 2, not 0. It is 0, which can only be reached through the
`return Vec::new()` arm.

## 3. Whether a fallback exists

Two facts constrain any fix, and both are in the code rather than in judgement:

- A partial cover cannot simply be emitted. `witness_tuples_for_group`
  (`qinst_egraph.rs:5393`) keeps a joined substitution only when
  `complete` — every variable bound — so a trigger covering 10 of 11 variables
  produces zero tuples, not partial ones.
- The uncovered variable in the worked case is not merely untriggered, it is
  **determined**: `(= ?v7 f9)` in guard position means every useful instance has
  `?v7 := f9`. Eliminating it is the textbook rewrite (destructive equality
  resolution): `∀x⃗. (x = t) → φ` with `x ∉ vars(t)` is equivalent to
  `∀x⃗\{x}. φ[x := t]`. It shrinks the universal instead of widening the search.

Whether that fallback reaches a **verdict** depends on a second measurement,
recorded in the next section: a nested registration compiled with
`active == false` and `context == None` has every tuple it produces discarded
(`qinst_egraph.rs:4870`, `:4934`), so giving such a universal a trigger changes
nothing at all. The distinct count above does not distinguish those, and it must.

<!-- Q1: sections 4 (active/context split) and the verdict follow. -->
