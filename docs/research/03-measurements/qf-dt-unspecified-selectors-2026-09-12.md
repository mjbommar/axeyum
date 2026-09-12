# QF_DT: what a wrong-constructor selector is worth, and what pinning it cost

Measured 2026-09-12 on `s4`, release binaries, 24 s wall per file, both arms
**interleaved per file** and pinned to the same four P-cores, so load and drift
cannot land on one arm. Lane `qf-dt-fold`. The decision this note supports is
[ADR-1930](../09-decisions/adr-1930-a-wrong-constructor-selector-is-unspecified-not-defaulted.md).

**The answer in one line: the blocker was not the fold, it was what the fold
would fold TO — and the convention it would have folded to was already producing
a wrong `unsat`.**

## The wrong `unsat`, first

Five lines of pure `QF_DT`:

```smt2
(set-logic QF_DT)
(declare-datatypes ((Opt 0)) (((none) (some (v Bool)))))
(declare-fun o () Opt)
(assert ((_ is none) o))
(assert (v o))
(check-sat)
```

| | verdict |
|---|---|
| axeyum, `main` at `1a53eea8e` | **`unsat`** |
| cvc5 1.3.4 | `sat` |
| z3 | `sat` |

`(v o)` reads `some`'s field off a `none` value. SMT-LIB leaves that value
unspecified, so the formula is satisfiable — pick an interpretation in which it
is true. `datatype_native` instead asserted the evaluator's total convention
into the reduced query (`tag_o == j OR f_{o,j,i} == default`), which deletes
exactly those interpretations. Three more probes, same protocol:

| probe | main | after | cvc5 | z3 |
|---|---|---|---|---|
| `((_ is none) o) AND (v o)` | **`unsat`** | `sat` | `sat` | `sat` |
| `((_ is none) o) AND (= (v o) #x05)` (logic `ALL`) | **`unsat`** | `sat` | `sat` | `sat` |
| `((_ is succ) (pred zero))` — verbatim from `v1l20044.cvc.smt2` | `unknown` | `sat` | `sat` | `sat` |
| `((_ is zero) x) AND ((_ is succ) (pred x))` | `unknown` | `unknown` | `sat` | `sat` |

## Why nothing caught it

Two guards existed and neither could fire.

- `tests/datatype_native.rs::select_on_wrong_constructor_nonzero_is_unsat`
  **asserted the wrong answer**, with a comment explaining the convention. A
  test defends the semantics it was told.
- `tests/qf_dt_differential_fuzz.rs` cross-checks 1,500 instances against z3 and
  reports `0 DISAGREE`. Its generator builds **enum** datatypes — every
  constructor nullary — so there is no selector to apply. The degenerate
  argument is not rare in its distribution; it is **outside its grammar**.

Stated as a measurement rather than an argument: with the default guard restored
(the mutant), `tests/qf_dt_selector_differential_fuzz.rs` fails at **seed 2**,
the second instance it generates, while `qf_dt_differential_fuzz` stays green at
1,500 / 1,500 agreeing.

## The division

`bench-results/parity-lists/QF_DT.txt` — the 200-file stride sample already
pinned for the 2026-09-11 board. 24 s / file, both arms interleaved.

| | decided |
|---|---|
| before (`main`, this run) | **113 / 200** |
| before (recorded board, 2026-09-11) | 114 / 200 |
| after | **168 / 200** |
| cvc5 / z3 (board) | 192 / 200 |

+55 files. **0 decided→undecided. 0 `sat`↔`unsat` flips.**

The one file where this run's before-arm disagrees with the recorded board is
`20210312-Bouvier/vlsat3_b84.smt2`, which the board decided and this run's
before-arm hit the watchdog on — a load-sensitive file, and it decides in the
after arm. The before baseline is quoted as 113 because that is what **this
machine** produced under **these conditions**; the board's 114 is the honest
comparison for the division's public row.

### Every decided file, re-checked live against both references

Not against the board's recorded column — re-run, at the same 24 s budget:

```
checked=168 disagreements=0
```

Coverage, because an empty disagreement list is only evidence if the check ran
against something: **168 of 168** carry a declared `:status` (107 `unsat`,
61 `sat`) and were compared against it; **165 of 168** also got a live `sat`
or `unsat` from cvc5 1.3.4 **and** from z3 (3 files, all `vlsat3`, exceeded the
reference budget). Zero disagreements on all three sources.

The checker's exit status depends on the finding, and it was shown to fire:
flipping one row's verdict in its input yields `checked=3 disagreements=3` and
exit 1.

## Where the gap went

Reason census over the undecided files, `--timeout-ms 8000`, `--trace`:

| reason | before | after round 1 | after |
|---|---:|---:|---:|
| `is`/`select` over a non-variable datatype term | 70 (of 81 gap files) | 53 | **0** |
| the traversed-field relaxation is incomplete | — | 19 | **32** |
| watchdog | — | 2 | 0 |
| **total undecided** | 86 | 74 | **32** |

The `before` column is lane WHY-UNKNOWN's census of the 81-file addressable gap
(2026-09-12); the two `after` columns are this lane's, over the whole undecided
set at `--timeout-ms 8000`. The final column is **one reason, 32 of 32** — the
undecided remainder of this division is now a single named class.

The class the brief was aimed at is closed. Every `typed_` file and every
`blocksworld` file now decides. What remains is **one** class, and it is a
different one: `unfold_traversals` replaces a `select` into a *datatype-typed*
field by a fresh free child variable, and `build_dt_eq` does not compare
datatype-typed fields, so two symbols an equality forces together can be given
children that differ. The replay catches it and the verdict is `unknown`. The
repair is to compare linked children in `build_dt_eq` — exact wherever both
sides are traversed, still a relaxation where only one is. That is the next
lane's work and it is sized: 32 files on this sample.

## What each change was worth

Round 1 (the unspecified-selector semantics plus the canonicalizer fold) took
114 → 126 on its own A/B and left 53 files still refusing. Round 2 (the `ite`
lift, the nested constructor equality, the linked-child witnesses, and the
vacuous-conjunct fix) took it to 168. Round 2 is the larger half, and it is worth being precise about
why: those rewrites were never *blocked* by the semantics work, but each of them
routes a query into the expansion, and the expansion was producing wrong answers
until round 1. Landing them in the other order would have widened the wrong
`unsat`'s reach.

Round 1's A/B also LOST two files (`vlsat3_b84`, `vlsat3_h27`), which is what
sent round 2 looking for the vacuous conjunct. The final A/B loses none.

Both the round-2 and the final A/B were run end to end on the 200, from two
separately built binaries, and produced the **same** 113 / 168 / +55 / 0 lost /
0 flipped / 0 disagreements. That is the reproducibility check on the number,
not a second opinion about the change.

The vacuous-conjunct fix is the one the A/B earned. `build_dt_eq`'s guarded form
contributes `tag_l != j OR true` for a constructor with no expanded field; a
pure enum has one such constructor **per value**, `vlsat3` declares hundreds, and
two files that decided in under 24 s stopped deciding. Nothing but a
decided→undecided check finds that: the change is correct, the tests stay green,
and the cost is entirely in the term count.
