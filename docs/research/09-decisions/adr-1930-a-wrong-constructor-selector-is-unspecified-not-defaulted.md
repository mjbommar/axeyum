# ADR-1930: A wrong-constructor selector read is UNSPECIFIED, not defaulted — the totality convention was a model restriction and it shipped a wrong `unsat`

Status: accepted
Index-summary: `((_ is none) o) AND (v o)` over the two-constructor `Opt` (`none`, or `some` carrying a `Bool`) — five lines of pure QF_DT — answered **`unsat`** on main while cvc5 1.3.4 and z3 both answer `sat`. SMT-LIB leaves `sel_{c,i}(t)` UNSPECIFIED when `t` was not built by `c`, so a formula is `unsat` only if it is false under EVERY choice of selector interpretation; ADR-0022's step-B gate instead fixed ONE choice (`well_founded_default`) and pinned it into the reduction with a guard `tag_o == j OR f_{o,j,i} == default`. A convention that is only ever *read* is harmless; one that is *asserted* removes models, and removing models is how a solver manufactures a wrong `unsat`. The suite asserted the wrong answer by name (`select_on_wrong_constructor_nonzero_is_unsat`), and the QF_DT differential fuzz could not have caught it: it generates ENUM datatypes only, so every constructor is nullary and it has no selector to apply — the exact blindness CLAUDE.md's "underspecified operators carry a fuzz seed-class that generates the degenerate argument" rule names. Decision: **the non-active field variable is FREE**, `build_dt_eq` guards field equality per constructor instead of leaning on the pins, `select_{c,i}(construct_d(...))` with `d != c` is abstracted to a fresh variable instead of refused, and the values the search picks are folded into ONE interpretation keyed by `(constructor, index, the operand's VALUE)` — carried on `Assignment`/`Model` beside the existing real-division-by-zero witnesses, and checked by the `sat` replay against the original assertions. Keying by the operand's VALUE is what makes the recorded interpretation congruent; a candidate that wants two results at one key describes no interpretation and yields `unknown`, never a verdict.
Date: 2026-09-12

## Context

`QF_DT` stood at 114/200 against cvc5's and z3's 192 (`bench-results/PARITY.md`,
measured 2026-09-11). Lane WHY-UNKNOWN's census attributed **70 of the 81
addressable-gap files to one sentence from one function** — `datatype_native.rs`
`expect_dt_symbol`, *"`is`/`select` over a non-variable datatype term
(constructors should fold first)"* — and a second defect on 73 of 81, where the
canonicalizer refused a datatype-sorted term outright and the query lost its
whole preprocessing pass.

The brief was to fold those shapes. Folding them turned out to be the second
question. The first is what the fold would fold *to*.

## What was measured

`sel_{c,i}(t)` where `t` was not built by `c` — `(pred zero)`, `(car null)`,
`(v o)` where `o` is `none` — is the case SMT-LIB leaves unspecified. ADR-0022's
step B chose a **total convention** for the evaluator: return
`well_founded_default` of the field's sort. That part is fine and necessary; the
evaluator must be total.

What was not fine is that `datatype_native` then **asserted** the convention into
the reduced query, as a guard per non-active field:

```
tag_o == j  OR  f_{o,j,i} == default
```

Four probes, run against the shipped `main` binary and both references at the
board's 24 s budget:

| probe | axeyum (main) | cvc5 1.3.4 | z3 |
|---|---|---|---|
| `((_ is none) o) AND (v o)`, `Opt = none \| some(v: Bool)` — pure QF_DT | **`unsat`** | `sat` | `sat` |
| `((_ is none) o) AND (= (v o) #x05)` | **`unsat`** | `sat` | `sat` |
| `((_ is succ) (pred zero))` — verbatim from `v1l20044.cvc.smt2` | `unknown` | `sat` | `sat` |
| `((_ is zero) x) AND ((_ is succ) (pred x))` | `unknown` | `sat` | `sat` |

The first two are **wrong `unsat`s**, not refusals. They did not show up on the
QF_DT board because pure `QF_DT` has no `Int`/`BitVec` sorts, so a benchmark in
that division can only reach the bug through a `Bool` field — and because the
corpus shapes that would reach it were being refused for the *other* reason
above. The bug is live in every logic that admits datatypes plus a scalar sort.

Two guards that should have caught it did not, for structural reasons worth
recording:

- `tests/datatype_native.rs::select_on_wrong_constructor_nonzero_is_unsat`
  asserted the wrong answer as the expected one, with a comment explaining the
  convention. A test can only defend the semantics it was told.
- `tests/qf_dt_differential_fuzz.rs` cross-checks against z3 on 1,500 instances
  and finds nothing, because its generator builds **enum** datatypes: every
  constructor is nullary, so no selector exists to apply and the degenerate
  argument is not merely rare in the distribution, it is **outside the
  grammar**. This is the failure mode CLAUDE.md's hard rule was written for,
  reproduced exactly.

## Decision

**A wrong-constructor selector read is unspecified, and the model says what it
chose.** Concretely:

1. **No default guard.** A non-active field variable `f_{o,j,i}` is free. This
   is a relaxation of the reduced query, so `unsat` still transfers — and it
   stops removing the models that made the wrong `unsat`.

2. **`build_dt_eq` guards per constructor.** It previously conjoined field
   equality across *every* constructor, exact only because both sides were
   pinned to the same default. Without the pins that form demands agreement on
   slots neither value uses — an over-constraint, i.e. the same wrong-`unsat`
   by another route. It now emits `tag_l == tag_r AND ⋀_j (tag_l == j ->
   j's fields agree)`, which is exact with no pinning. A constructor with no
   expanded field contributes nothing and is skipped: a pure enum has one such
   constructor *per value*, the `vlsat3` family declares hundreds, and emitting
   the vacuous conjunct cost two files that previously decided (measured, then
   fixed).

3. **`select_{c,i}(construct_d(...))` with `d != c` is abstracted**, not
   refused: a fresh free variable of the field's sort. Read-over-construct
   already folds `d == c` exactly, so this is precisely the unspecified residue.

4. **The chosen values become one interpretation.** `Assignment` and `Model`
   carry `dt_select_wrong_ctor`, keyed by `(constructor, index, the operand's
   VALUE)` — the same shape as the existing `real_div_zero` witnesses for
   SMT-LIB's other unspecified operator. The evaluator's `DtSelect`
   wrong-constructor arm consults it and falls back to `well_founded_default` on
   a miss, so an empty table is exactly the previous behaviour. The `sat` replay
   runs against the **original** assertions under that interpretation.

Keying by the operand's **value** rather than its term is the load-bearing
detail: it makes the recorded interpretation a function of the value, hence
congruent, which the relaxation in (1) and (3) does not enforce on its own.
`x = zero AND (pred x) != (pred zero)` is unsatisfiable and the reduced query is
satisfiable; the conflict shows up as two different values at one key, and the
verdict becomes `unknown`.

Soundness, in one line per direction. **`unsat`**: every step above only enlarges
the reduced query's model space, and every real model (values plus *any*
selector interpretation) maps into it, so reduced-`unsat` implies
original-`unsat`. **`sat`**: the returned interpretation is total (defaults
outside the table) and congruent (keyed by value), and the original assertions
evaluate true under it, so a model exists.

### Also: the canonicalizer's vacuous constant fold

`all_constant` is vacuously true for a **nullary** application, so every nullary
datatype constructor (`nil`, `zero`, an enum member) reached `value_to_term` and
raised `sort mismatch: expected Bool or BitVec, found (Datatype n)`.
`canonicalize_terms` has no partial-failure mode, so one such subterm cost the
whole query its entire preprocessing pass — the 73-of-81 defect. The fold now
declines, which is the identity rewrite.

### Also: `ite` lifting and nested constructor equalities

Two denotation-preserving rewrites in `simplify_datatypes` that the refusal was
standing in for:

- a datatype-sorted `ite` is lifted out of `is` / `select` / `=`
  (`sel_c(ite(b,x,y))` → `ite(b, sel_c(x), sel_c(y))`), bounded at 64 branch
  combinations because an equality with an `ite` on each side multiplies;
- `expand_constructor_eq` re-folds each per-field equality, so a field that is
  itself a constructor expands too. Building it with a raw `arena.eq` left a
  constructor standing on one side of an equality, which the native route
  refuses — and `(= (cons (node null) (children (leaf x1))) x4)` is one
  assertion from one corpus file.

## Consequences

- `QF_DT` on the pinned 200, A/B interleaved per file: see
  `docs/research/03-measurements/qf-dt-unspecified-selectors-2026-09-12.md`.
- `tests/qf_dt_selector_differential_fuzz.rs` is new: the same z3 cross-check as
  the enum fuzz, over a datatype with `Bool`-carrying constructors, and its
  generator emits the degenerate argument deliberately — a selector read over a
  variable the formula forces to another constructor, and over an explicit
  constructor application with both a matching and a non-matching constructor.
  Its agreement floor is part of the assertion: a run in which axeyum declines
  everything would report "0 DISAGREE" while checking nothing.
- The evaluator's total convention is unchanged and still the fallback. What
  changed is that nothing **asserts** it any more.
- The general rule, which is not about datatypes: **a chosen-total convention
  for an underspecified operator is sound to READ and unsound to ASSERT.** The
  evaluator may return a default so that replay is total; the reduction may not
  constrain the solver to it. `bvudiv x 0` is safe because SMT-LIB *fixes* it;
  `(/ x 0)` was already handled the right way, with a model-carried witness.
  Datatype selectors are the third such operator and were handled the wrong way.
