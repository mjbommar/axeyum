# Lane: skeleton-reach — where the skeleton shape is, and what stops us reaching it

<!-- plan-section: lane-status -->

**Lane skeleton-reach (`DONE`, skeleton-reach, 2026-09-14).** Extends
[ADR-2025]'s boolean-skeleton rung — the one lever that worked this week —
rather than opening an eleventh hypothesis. Rules
[pre-registered](../../../bench-results/skeleton-reach-20260914/PREREGISTRATION.md)
in their own commit before anything was built or measured.

Branch base: `git merge-base main HEAD` is
`b32867a21b37dcb0f12c75d81557c8eabf6b25a4`, which **is** local `main`'s HEAD.

## 1. `fd:parse` on `UFNIA` is 7 of 147, and it is TWO causes

All 200 `UFNIA` files, verdicts **re-derived in the same run** (147 undecided,
matching the `tier1-current` sample exactly). `bound_by` over the undecided:

    q:egraph 81 · q:mbqi 41 · NONE 12 · fd:parse 7 · uf-arithmetic 6

Splitting the `fd:parse` bucket by the raw give-up detail rather than by the
label:

| kind | n | detail |
|---|---:|---|
| `ResourceLimit` | **5** | `distinct` over the pairwise-expansion cap |
| `Error` | **2** | `parse error: fp exponent field must be a bit-vector` |

The second is a **name-capture bug**. `apply_op` tries every theory-operator
arm before the fall-through that consults `arena.find_function`, so a script
carrying `(declare-fun fp (Int Int Int) Int)` never reaches its own
declaration. `fp` is a FloatingPoint theory symbol; those scripts are `UFNIA`,
which has no FloatingPoint theory, so the name is legal there and both z3 and
cvc5 accept it. **180 files corpus-wide**, all `UFNIA`, zero in the other six
Tier 1 division directories.

The two counts cross-validate: an independent static scan of the corpus finds
exactly **5 over-cap + 2 shadowed = 7** among the same 147 rows.

## 2. Why only `UFLIA` moved: the shape is REACHED and NOT REFUTABLE

A static instrument over **all 655 undecided rows** of the seven Tier 1
divisions — no axeyum binary involved — abstracts every maximal quantified
subformula to one opaque atom and asks cvc5 **and** z3 whether the remainder is
already unsat. 0 disagreements at 514 comparable rows.

| division | n | shape ABSENT | NOT MEASURED | skeleton-`unsat` |
|---|---:|---:|---:|---:|
| `AUFLIRA` | 36 | 0 | 0 | **6** |
| `UFNIA` | 147 | 0 | 25 | **5** |
| `UF` | 106 | 0 | 0 | 1 |
| `UFLIA` | 115 | 0 | 0 | 1 |
| `AUFDTLIRA` | 79 | 0 | 0 | 0 |
| `UFDTLIRA` | 56 | 0 | 0 | 0 |
| `QF_NIA` | 116 | **116** | 0 | 0 |

Those 13 rows against our own binary:

| | n | what it means |
|---|---:|---|
| **NOT REFUTABLE** | **9** | the rung **runs** and declines |
| **NOT REACHED** | **4** | all `UFNIA`, all `fd:parse` — §1's two causes |
| absent | — | `QF_NIA` 116/116 (quantifier-free by construction) |

**So the answer is neither "absent" nor "not reached": it is NOT REFUTABLE,
9 of 13**, across `AUFLIRA` 6, `UF` 1, `UFLIA` 1, `UFNIA` 1. Our ground checker
cannot refute a skeleton that cvc5 and z3 both refute. That is [ADR-2025]'s
`CAPABILITY-LIMIT` bucket, now sized across four divisions, and it is much the
largest of the three. **`AUFLIRA` was on nobody's list and holds the most of
it.**

## 3. The composition nobody could have measured before yesterday

Each fix alone is worth ~nothing on these rows; the question is whether they
COMPOSE with the rung that landed a day later.

* [ADR-2000] measured the linear `distinct` encoding on 2026-09-13 at +1 of
  356 and shipped it **Off**, concluding "the quantified ladder is the binding
  constraint, at any budget". True then.
* [ADR-2025]'s rung landed 2026-09-14 and **does not enter the quantified
  ladder at all**.
* A file refused at **ingest** reaches neither.

Preflight on `UFNIA/vcc-havoc/verisoft-baby.c.10.privileged.smt2`, one binary
and two env values:

    base  bound_by=fd:parse       unknown   giveup=fp exponent field must be a bit-vector
    arm   bound_by=q:bool-skeleton unsat    103 ms

## 4. What shipped

`crates/axeyum-smtlib/src/parse.rs` — a user `declare-fun` outranks the theory
operator arm of the same name, **when the declared signature matches the
application exactly**, so an arity or sort mismatch falls through to the arm it
would have taken. Behind `AXEYUM_DECLARED_NAME_WINS`, **shipping Off**.

Registered as `smtlib-declared-name-wins` in `mutation_controls.py`. Its first
run found a real hole — the **arity guard SURVIVED**, because the fixture tested
too FEW arguments and `zip` stops at the shorter side, so relaxing `==` to `<=`
still rejected it. With the too-many case added, all three guards kill.

## 5. The A/B, and the decision the rule made

Interleaved per file, one binary and two env values, 8 pinned pairs held fixed
across every phase.

| run | rows | base | arm | net | GAIN | LOSS | FLIP |
|---|---:|---:|---:|---:|---:|---:|---:|
| treatment `UFNIA` | 200 | 53 | **55** | **+2** | 2 | 0 | 0 |
| noise floor (same arm twice) | 200 | 53 | 53 | **0** | 0 | 0 | 0 |
| control `QF_NIA` | 200 | 84 | 84 | **0** | 1 | 1 | 0 |

**All seven `fd:parse` rows lose the ingest refusal and reach the ladder**; two
convert (60 ms, 130 ms), four then hit the watchdog, one hits a different
`ResourceLimit`. Both gains 2/2 STABLE-GAIN over three passes per arm, 0
authority disagreements at a full 2/2 comparable denominator.

**R9 was pre-registered at ≥ 5 net. +2 does not meet it, so the lever ships
`Off`** — and that rule was written for a gain lever, while the `fp` capture is
a correctness defect that rejects 180 legal scripts. [ADR-2040] states both and
does not fold one into the other.

**The control is WEAK and is reported as weak**: its only over-cap row is a
`let`-binding site [ADR-2000]'s polarity walk declines, so the lever fired on 0
of 200 there.

## 6. The decisive follow-up: with reach fixed, it is all CAPABILITY

All 13 skeleton-unsat rows, both reach levers armed, at 24 s **and** at 5x:

| | n |
|---|---:|
| **CAPABILITY-LIMIT** (declines at both) | **11** |
| CONVERTED | 2 |
| **BUDGET-LIMIT** | **0** |
| **RUNG-NEVER-REACHED** | **0** |

`RUNG-NEVER-REACHED` was 4 before this lane and is 0 after it, so the reach
question is **closed** and was worth exactly 2. `BUDGET-LIMIT` at 0 says a
budget lever buys nothing.

## Next

The 11 CAPABILITY rows are the largest single lead this lane found and are not
this lane's to fix: a quantifier-free query, no instantiation, no admission
bound, refuted by cvc5 **and** z3 and not by us. `AUFLIRA` holds 6 of them. It
is the ground checker, the same component [ADR-2020] left open.

Also open and untouched here: the **12 undecided `UFNIA` rows with no route
line at all** (the watchdog fires before the worker returns), and the **47 of
356 over-cap `distinct` sites** [ADR-2000]'s polarity walk declines.

[ADR-2000]: ../../research/09-decisions/adr-2000-the-front-door-refusal-was-not-the-binding-constraint.md
[ADR-2020]: ../../research/09-decisions/adr-2020-the-ground-checker-mostly-refuses-and-the-set-it-refuses-is-one-we-had-no-need-to-build.md
[ADR-2025]: ../../research/09-decisions/adr-2025-the-refutation-was-available-before-instantiating-and-we-dropped-the-assertion-carrying-it.md
[ADR-2040]: ../../research/09-decisions/adr-2040-the-reach-half-is-worth-two-and-the-whole-remaining-shape-is-the-ground-checker.md
