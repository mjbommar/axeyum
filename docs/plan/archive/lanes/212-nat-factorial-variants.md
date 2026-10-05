# Lane: nat-factorial-variants — landing `Nat.descFactorial` and its boundary lemmas

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-factorial-variants, 2026-08-28).** Task named
three absent definitions blocking five open `F:ml430-nat-*` facts:
`Nat.ascFactorial`, `Nat.descFactorial`, `Nat.multichoose`. Landed the first
one named as the priority ("take descFactorial first ... landing ONE
definition with its boundary lemmas is a complete success"):
`Nat.descFactorial` in `crates/axeyum-lean-kernel/src/nat_prelude/desc_factorial.rs`,
structural recursion on its **second** argument via `NatOps::define_binary`
(the same combinator `Nat.sub`/`Nat.mul` use), so `descFactorial_zero` /
`descFactorial_succ` hold by `Eq.refl`. No fuel device needed, matching the
prediction. Plus two derived boundary theorems: `descFactorial_one`
(`n.descFactorial 1 = n`, closed by `mul_one`'s own proof term against a
purely-defeq goal, no rewrite) and `descFactorial_of_lt`
(`n < k -> n.descFactorial k = 0`, by induction on `k` with `n` held fixed,
explicitly exercising `Nat.sub`'s truncation -- the flagged highest-risk
seam).

`Nat.ascFactorial` and `Nat.multichoose` were **not** attempted this session
(scope discipline per the brief: one definition landed well beats three
started). They remain open/blocked for a future lane.

Measured `nat` trusted surface after this lane:
`nat: axiom=0 opaque=0 quotient=0 total_trusted=0` (`nat_axiom_inventory
--require-axiom-free nat`, exit 0). `cargo test -p axeyum-lean-kernel --lib
nat_prelude::` : 105 passed, 0 failed (confirmed nonzero, up from 104 before
this lane -- one new concrete-instantiation test added). `the_build_is_deterministic`'s
pin recomputed from its own panic message: `74 + 383` -> `75 + 387` (1
definition + 4 theorems added), not hand-counted.

Four new facts created (`F-nat-desc-factorial-{zero,succ,one,of-lt}.json`);
no `F:ml430-*` mirror fact flipped by hand -- those name Mathlib's own
`Nat.descFactorial` and remain untouched, including
`F:ml430-nat-factorial-dvd-descfactorial-bbf6124f` (the specific fact named
as blocked in the task), which is NOT closed by this lane: the divisibility
theorem (`k! | n.descFactorial k`) needs an induction this session did not
attempt (it is not a simple induction on `k` alone -- the natural argument
needs a Pascal's-rule-shaped step this lane judged out of scope for "one
definition + boundary lemmas"). No target this lane touched carried a
HELD-OUT or MUTATION marker.

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-factorial-variants | `Nat.descFactorial` + `descFactorial_zero`/`_succ`/`_one`/`_of_lt`, axiom-free, `nat_prelude` sweep 105/105; 4 new `F:nat-desc-factorial-*` facts; `Nat.ascFactorial`/`Nat.multichoose` left for a future lane |
