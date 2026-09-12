# Lane: qf-dt-fold — the QF_DT gap, and the wrong `unsat` under it

<!-- plan-section: lane-status -->

**Lane qf-dt-fold (`DONE`, qf-dt-fold, 2026-09-12).** `QF_DT` **114 → 168 of
200** against cvc5's and z3's 192; the gap closes from **+78 to +24**. On the
pinned 200 with the arms interleaved per file: **+55 decided, 0
decided→undecided, 0 `sat`↔`unsat` flips, 0 disagreements** — every one of the
168 decided files re-checked live against its declared `:status` and against
cvc5 1.3.4 and z3 at the same budget. Two separately built binaries reproduced
the identical row.

**The lane was sent to fold `is`/`select` over constructors. The fold was the
second question; the first was what it would fold TO, and the answer was a
SHIPPED WRONG `unsat`.** Five lines of pure `QF_DT` —
`((_ is none) o) AND (v o)` over `Opt = none | some(v: Bool)` — answered `unsat`
on `main` while cvc5 and z3 both answer `sat`. SMT-LIB leaves `sel_{c,i}(t)`
UNSPECIFIED when `t` was not built by `c`; ADR-0022's step-B convention
(`well_founded_default`) was not merely *read* by the evaluator, it was
**asserted** into the reduction as `tag_o == j OR f_{o,j,i} == default`, and
asserting a choice over an unspecified operator deletes models. The unit suite
asserted the wrong answer by name, and the `QF_DT` differential fuzz generates
ENUM datatypes only — every constructor nullary — so the degenerate argument was
**outside its grammar**, not merely rare in it.

Decided by
[ADR-1930](../../research/09-decisions/adr-1930-a-wrong-constructor-selector-is-unspecified-not-defaulted.md);
measurement in
[qf-dt-unspecified-selectors-2026-09-12.md](../../research/03-measurements/qf-dt-unspecified-selectors-2026-09-12.md).
The new oracle gate is `tests/qf_dt_selector_differential_fuzz.rs`: with the
default guard restored it fails at **seed 2**, the second instance it generates,
while the enum fuzz stays green at 1,500 / 1,500.

**What remains is one class, and it is sized.** All 32 undecided files give the
same reason: `unfold_traversals` replaces a `select` into a *datatype-typed*
field by a fresh free child variable, and `build_dt_eq` does not compare
datatype-typed fields, so two symbols an equality forces together can be given
children that differ; the replay catches it and the verdict is `unknown`. The
repair is to compare linked children in `build_dt_eq` — exact where both sides
are traversed, still a relaxation where only one is.

**The general rule, which is not about datatypes: a chosen-total convention for
an underspecified operator is sound to READ and unsound to ASSERT.** The
evaluator may return a default so replay stays total; the reduction may not
constrain the solver to it. `bvudiv x 0` is safe because SMT-LIB *fixes* it;
`(/ x 0)` was already handled the right way, with a model-carried witness keyed
by the numerator VALUE. Selectors are now handled the same way, keyed by
`(constructor, index, operand value)` — the value, not the term, because that is
what makes the recorded interpretation congruent.

<!-- plan-section: landed-changes -->

| 2026-09-12 | `f6e616c0e` | `QF_DT` wrong `unsat` fixed: an unspecified selector read is model-chosen, not defaulted (ADR-1930) |
| 2026-09-12 | `09aeb970c` | datatype `ite` lifting, nested constructor equalities, linked-child witnesses, and the selector differential fuzz |
