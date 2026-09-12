# ADR-1930: Two wrong `unsat`s in QF_DT, one shape — a convention the evaluator READS was ASSERTED into the reduction

Status: accepted
Index-summary: Two wrong `unsat`s, found by asking what a fold over `is`/`select` would fold TO. (1) `((_ is none) o) AND (v o)` over the two-constructor `Opt` — five lines of pure QF_DT — answered **`unsat`** while cvc5 1.3.4 and z3 both answer `sat`: SMT-LIB leaves `sel_{c,i}(t)` UNSPECIFIED when `t` was not built by `c`, and ADR-0022's step-B totality convention was not merely READ by the evaluator, it was ASSERTED into the reduction as `tag_o == j OR f_{o,j,i} == default`. (2) `is-cons(a) AND is-cons(b) AND a != b` over a list whose every field is a datatype also answered **`unsat`**: `build_dt_eq` skips fields it cannot compare, which makes the encoded equality WEAKER than real equality — and weaker in a POSITIVE occurrence is STRONGER under a negation, so "it is a relaxation, so `unsat` is sound" was only half true. The suite asserted the first answer by name and the differential fuzz could not generate either shape: it builds ENUM datatypes, so no selector and no field exists to compare. Decision: the non-active field variable is FREE and the model CARRIES the selector interpretation it chose, keyed by `(constructor, index, the operand's VALUE)` so it is congruent; and structural equality gets TWO encodings, a restriction that may only yield `sat` (replay-checked, and it is the only one that can witness a difference) and a relaxation that may yield `unsat`. QF_DT 114/200 -> **171/200** on the pinned parity list, +57, **0 decided->undecided, 0 flips, 0 disagreements** against the declared `:status` and against cvc5 1.3.4 and z3 re-run live. The general rule: **a chosen-total convention for an underspecified operator is sound to READ and unsound to ASSERT.**
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

## The second wrong `unsat`, found by the first

`build_dt_eq` reduces `o == o'` to `tag_l == tag_r` conjoined with equality of
the fields that HAVE an expansion variable. A datatype-typed field has none, so
it is skipped, and the function's own comment said that was "a weaker
(relaxation) constraint: sound for `unsat`".

Weaker is a relaxation in a **positive** occurrence. Under a negation it is a
**strengthening**, and `unsat` is exactly the verdict a strengthening may not
give. On `list = cons(car: tree, cdr: list) | null`, whose every field is a
datatype:

```smt2
(assert ((_ is cons) a))
(assert ((_ is cons) b))
(assert (not (= a b)))
```

reduces to `tag_a == cons AND tag_b == cons AND tag_a != tag_b` and answers
**`unsat`**. cvc5 1.3.4 and z3 both answer `sat`; two `cons` values with
different heads plainly exist. Measured 2026-09-12, on `main` and on this
lane's first two commits.

The repair is not to pick a better single encoding — there is no single formula
over the tags and the comparable fields that is equivalent to real equality when
a field cannot be compared. **There are two encodings, sound for opposite
verdicts:**

| encoding | relation to real equality | verdict it may give |
|---|---|---|
| restriction — the plain conjunction above | weaker positively, **stronger** negatively | only `sat`, and only replay-checked |
| relaxation — a free Boolean carrying just the conditions the expansion can decide | every real model extends to it in **both** polarities | `unsat` transfers; `sat` replay-checked |

So the route runs the restriction first (it is the only one that can WITNESS a
difference, which is what a `sat` model needs) and falls back to the relaxation
for everything else. When no equality is inexact the two coincide and one pass
does. The relaxation additionally expands a structural equality one level into
its per-constructor field comparison — exact, and it is what gives `a != b` a
witness at depth 1 through the child variables `unfold_traversals` already
mints.

## Decision

**A wrong-constructor selector read is unspecified, and the model says what it
chose. Structural equality that cannot be compared exactly gets two encodings,
and neither one's unfavourable verdict is believed.** Concretely:

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

- `QF_DT` on the pinned 200, A/B interleaved per file: **114 -> 171**, +57,
  0 decided->undecided, 0 flips, 0 disagreements. See
  [the measurement](../03-measurements/qf-dt-unspecified-selectors-2026-09-12.md).
- Two new z3 cross-checks, one per wrong `unsat`, each with a generator that
  emits its degenerate argument **deliberately** and an agreement floor in the
  assertion (a run that declines everything would otherwise report "0 DISAGREE"
  while checking nothing):
  `tests/qf_dt_selector_differential_fuzz.rs` (a datatype with `Bool`-carrying
  constructors; a selector read over a variable the formula forces to another
  constructor, and over an explicit constructor application with both a matching
  and a non-matching constructor) and
  `tests/qf_dt_equality_differential_fuzz.rs` (a datatype whose middle
  constructor carries another datatype, so it cannot be compared exactly).
  Restoring each defect kills its own suite: the selector fuzz at **seed 2**,
  the equality fuzz at **seed 40**, both with the offending instance printed.
- **The equality fuzz needed its degenerate case emitted as ONE atom.** Left to
  the random connective it survived all 1,500 seeds against the restored
  mutant, because the shape needs three conjuncts to line up at once and a
  disjunction is satisfiable as soon as one disjunct is. A grammar that CAN
  produce a shape is not a generator that DOES.
- The evaluator's total convention is unchanged and still the fallback. What
  changed is that nothing **asserts** it any more.
- The general rule, which is not about datatypes: **a chosen-total convention
  for an underspecified operator is sound to READ and unsound to ASSERT.** The
  evaluator may return a default so that replay is total; the reduction may not
  constrain the solver to it. `bvudiv x 0` is safe because SMT-LIB *fixes* it;
  `(/ x 0)` was already handled the right way, with a model-carried witness.
  Datatype selectors are the third such operator and were handled the wrong way.
