# QF_DT: what a wrong-constructor selector is worth, and what pinning it cost

Measured 2026-09-12 on `s4`, release binaries, 24 s wall per file, both arms
**interleaved per file** and pinned to the same four P-cores, so load and drift
cannot land on one arm. Lane `qf-dt-fold`. The decision this note supports is
[ADR-1930](../09-decisions/adr-1930-a-wrong-constructor-selector-is-unspecified-not-defaulted.md).

**The answer in one line: the blocker was not the fold, it was what the fold
would fold TO — and asking that question turned up TWO wrong `unsat`s, both of
which `main` was shipping.**

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
| `((_ is zero) x) AND ((_ is succ) (pred x))` | `unknown` | `sat` | `sat` | `sat` |
| `((_ is zero) x) AND ((_ is zero) y) AND (pred x) != (pred y)` | `unknown` | `unknown` | `unsat` | `unsat` |
| `is-cons(a) AND is-cons(b) AND a != b` (the second wrong `unsat`, below) | **`unsat`** | `sat` | `sat` | `sat` |

The last row is the congruence case and it is the honest one: `x` and `y` are
both `zero`, so `pred x` and `pred y` are the SAME unspecified value and the
query is `unsat`. The relaxation gives the two reads independent variables, the
replay refuses the candidate, and the verdict is `unknown` — incomplete, never
wrong.

## The second wrong `unsat`

```smt2
(set-logic QF_DT)
(declare-datatypes ((nat 0)(list 0))
  (((succ (pred nat)) (zero)) ((cons (car nat) (cdr list)) (null))))
(declare-fun a () list)
(declare-fun b () list)
(assert ((_ is cons) a))
(assert ((_ is cons) b))
(assert (not (= a b)))
(check-sat)
```

| | verdict |
|---|---|
| axeyum, `main` at `1a53eea8e` | **`unsat`** |
| cvc5 1.3.4 | `sat` |
| z3 | `sat` |

`build_dt_eq` compares the tag and the fields that have an expansion variable,
and skips the ones that do not. Every field of `list` is a datatype, so the
encoded equality reduces to `tag_a == tag_b` — WEAKER than real equality. Its
own comment said "weaker is a relaxation, so `unsat` is sound", and that is true
of a POSITIVE occurrence. Under the negation here, weaker becomes STRONGER: the
reduced query demands a tag difference the two testers forbid.

There is no single formula over the tags and the comparable fields that is
equivalent to real equality when a field cannot be compared. There are two, and
they are sound for opposite verdicts — the restriction can WITNESS a difference
(so it may give `sat`, replay-checked) and the relaxation admits every real
model in both polarities (so it may give `unsat`). The route runs the
restriction first and falls back.

## Why nothing caught it

Two guards existed and neither could fire.

- `tests/datatype_native.rs::select_on_wrong_constructor_nonzero_is_unsat`
  **asserted the wrong answer**, with a comment explaining the convention. A
  test defends the semantics it was told.
- `tests/qf_dt_differential_fuzz.rs` cross-checks 1,500 instances against z3 and
  reports `0 DISAGREE`. Its generator builds **enum** datatypes — every
  constructor nullary — so there is no selector to apply and no field to
  compare. Neither degenerate argument is rare in its distribution; both are
  **outside its grammar**.

Stated as a measurement rather than an argument. With each defect restored as a
mutant, the suite written for it dies and the enum fuzz does not:

| mutant | its own fuzz | enum fuzz |
|---|---|---|
| the default field guard | `qf_dt_selector_differential_fuzz` fails at **seed 2** | green, 1,500 / 1,500 |
| the restriction-only equality | `qf_dt_equality_differential_fuzz` fails at **seed 40** | green, 1,500 / 1,500 |

**A grammar that CAN produce a shape is not a generator that DOES.** The
equality fuzz's first draft could express `is-b(x) AND is-b(y) AND x != y` — the
atoms exist, the connective is `and` three times out of four — and it survived
all 1,500 seeds against its mutant. It catches the mutant only once that
conjunction is emitted as ONE atom. Three conjuncts have to line up at once, and
a disjunction is satisfiable as soon as one disjunct is.

## The division

`bench-results/parity-lists/QF_DT.txt` — the 200-file stride sample already
pinned for the 2026-09-11 board. 24 s / file, both arms interleaved.

| | decided |
|---|---|
| before (`main`) | **114 / 200** |
| after | **171 / 200** |
| cvc5 / z3 (board) | 192 / 200 |

+57 files. **0 decided→undecided. 0 `sat`↔`unsat` flips.** The division's gap
closes from **+78 to +21**.

`20210312-Bouvier/vlsat3_b84.smt2` is load-sensitive: it decided on the board
and in this run's before-arm, and an earlier before-arm run under heavier load
hit the watchdog on it. It decides in every after-arm run.

### Every decided file, re-checked live against both references

Not against the board's recorded column — re-run, at the same 24 s budget:

```
checked=171 disagreements=0
```

Coverage, because an empty disagreement list is only evidence if the check ran
against something: **171 of 171** carry a declared `:status` (107 `unsat`,
64 `sat`) and were compared against it; **168 of 171** also got a live `sat`
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
| the traversed-field relaxation is incomplete | — | 19 | **29** |
| watchdog | — | 2 | 0 |
| **total undecided** | 86 | 74 | **29** |

The `before` column is lane WHY-UNKNOWN's census of the 81-file addressable gap
(2026-09-12); the two `after` columns are this lane's, over the whole undecided
set at `--timeout-ms 8000`. The final column is **one reason, 29 of 29** — the
undecided remainder of this division is now a single named class.

The class the brief was aimed at is closed. Every `typed_` file and every
`blocksworld` file now decides. What remains is **one** class: a candidate whose
projected values agree where the original assertions need them to differ, on a
datatype field neither encoding can see past. One level of equality expansion
already buys most of it; the remaining 29 need a bounded unfolding to depth `k`
with the comparison left free at the cut — the standard construction, and the
next lane's work. It is sized: 29 files on this sample, all giving the same
`; give-up` line.

## What each change was worth

| step | decided |
|---|---:|
| `main` | 114 |
| + the unspecified-selector semantics, + the canonicalizer fold | 126 |
| + `ite` lifting, nested constructor equalities, linked-child witnesses | 168 |
| + the SOUND equality encoding, alone | 137 |
| + the restriction/relaxation split and depth-1 equality expansion | **171** |

The fourth row is the one worth reading. Making the equality encoding sound, on
its own, cost **31 files** — 30 of them `sat` results the replay could no longer
confirm, because the relaxation cannot witness a difference it cannot see. That
is the honest price of the fix, and it is why the answer is two encodings rather
than a better one: the restriction is the arm that witnesses, the relaxation is
the arm that refutes, and running both recovers the 31 and adds 3 more.

Round 1 (the unspecified-selector semantics plus the canonicalizer fold) took
114 → 126 on its own A/B and left 53 files still refusing. Round 2 (the `ite`
lift, the nested constructor equality, the linked-child witnesses, and the
vacuous-conjunct fix) took it to 168, and round 3 (the equality encoding) to
171. Round 2 is the larger half, and it is worth being precise about
why: those rewrites were never *blocked* by the semantics work, but each of them
routes a query into the expansion, and the expansion was producing wrong answers
until round 1. Landing them in the other order would have widened the wrong
`unsat`'s reach.

Round 1's A/B also LOST two files (`vlsat3_b84`, `vlsat3_h27`), which is what
sent round 2 looking for the vacuous conjunct. The final A/B loses none.

Round 2's number was run end to end twice, from two separately built binaries,
and reproduced exactly (168, +55, 0 lost, 0 flipped, 0 disagreements). That is
the reproducibility check on the measurement, not a second opinion about the
change.

The vacuous-conjunct fix is the one the A/B earned. `build_dt_eq`'s guarded form
contributes `tag_l != j OR true` for a constructor with no expanded field; a
pure enum has one such constructor **per value**, `vlsat3` declares hundreds, and
two files that decided in under 24 s stopped deciding. Nothing but a
decided→undecided check finds that: the change is correct, the tests stay green,
and the cost is entirely in the term count.
