# Lane: qf-dt-fold — the QF_DT gap, and the two wrong `unsat`s under it

<!-- plan-section: lane-status -->

**Lane qf-dt-fold (`DONE`, qf-dt-fold, 2026-09-12).** `QF_DT` **114 → 171 of
200** against cvc5's and z3's 192; the gap closes from **+78 to +21**. On the
pinned 200 with the arms interleaved per file: **+57 decided, 0
decided→undecided, 0 `sat`↔`unsat` flips, 0 disagreements** — every one of the
171 decided files re-checked LIVE against its declared `:status` (171 of 171)
and against cvc5 1.3.4 and z3 at the same budget (168 of 171; three `vlsat3`
files exceed the reference budget).

**The lane was sent to fold `is`/`select` over constructors. The fold was the
second question; the first was what it would fold TO, and asking it turned up
TWO SHIPPED WRONG `unsat`s.**

1. `((_ is none) o) AND (v o)` over a two-constructor `Opt` — five lines of pure
   `QF_DT` — answered `unsat` on `main`; cvc5 and z3 answer `sat`. SMT-LIB
   leaves `sel_{c,i}(t)` UNSPECIFIED when `t` was not built by `c`, and
   ADR-0022's step-B totality convention was not merely *read* by the evaluator,
   it was **asserted** into the reduction as `tag_o == j OR f_{o,j,i} ==
   default`. The unit suite asserted the wrong answer by name.
2. `is-cons(a) AND is-cons(b) AND a != b` over a list whose every field is a
   datatype also answered `unsat`. `build_dt_eq` skips fields it cannot compare,
   making the encoded equality WEAKER than real equality — and weaker in a
   POSITIVE occurrence is **stronger** under a negation, so its "it is a
   relaxation, so `unsat` is sound" comment was only half true.

Neither could be caught by the `QF_DT` differential fuzz: it builds ENUM
datatypes, so no selector exists to apply and no field exists to compare. Both
shapes were **outside its grammar**, not merely rare in its distribution.

Decided by
[ADR-1930](../../research/09-decisions/adr-1930-a-wrong-constructor-selector-is-unspecified-not-defaulted.md);
measurement in
[qf-dt-unspecified-selectors-2026-09-12.md](../../research/03-measurements/qf-dt-unspecified-selectors-2026-09-12.md).

**Two rules worth carrying out of this lane.**

- **A chosen-total convention for an underspecified operator is sound to READ
  and unsound to ASSERT.** The evaluator may return a default so replay stays
  total; the reduction may not constrain the solver to it. `bvudiv x 0` is safe
  because SMT-LIB *fixes* it; `(/ x 0)` was already handled the right way, with
  a model-carried witness keyed by the numerator VALUE. Selectors are now
  handled the same way, keyed by `(constructor, index, operand value)` — the
  value, not the term, because that is what makes the interpretation congruent.
- **A grammar that CAN produce a shape is not a generator that DOES.** The new
  equality fuzz could express its degenerate case from the start and still
  survived all 1,500 seeds against the restored defect; it catches it at seed 40
  only once that case is emitted as ONE atom. Three conjuncts have to line up at
  once, and a disjunction is satisfiable as soon as one disjunct is.

**What remains is one class, and it is sized.** All 29 undecided files give the
same `; give-up` line: a candidate whose projected values agree where the
assertions need them to differ, on a datatype field neither equality encoding
can see past. One level of expansion already buys most of it; the rest needs a
bounded unfolding to depth `k` with the comparison left free at the cut.

<!-- plan-section: landed-changes -->

| 2026-09-12 | `f6e616c0e` | `QF_DT` wrong `unsat` #1: an unspecified selector read is model-chosen, not defaulted (ADR-1930) |
| 2026-09-12 | `09aeb970c` | datatype `ite` lifting, nested constructor equalities, linked-child witnesses, and the selector differential fuzz |
| 2026-09-12 | `e75dc4a43` | ADR-1930 and the QF_DT measurement note |
