# Lane: nat-multichoose-facts — judge whether the three `ml430` multichoose mirrors may be flipped

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-multichoose-facts, 2026-08-28).** The three
target facts (`F:ml430-nat-multichoose-zero-right-6ef827c8`,
`F:ml430-nat-multichoose-one-b210386a`,
`F:ml430-nat-multichoose-one-right-7755072d`) and the `Nat.multichoose`
theorems they mirror had already landed the day before this lane started
(`nat_prelude/multichoose.rs`, three `declare_multichoose_*` theorems, the
paired local facts `F-nat-multichoose-zero-right.json` /
`F-nat-multichoose-one.json` / `F-nat-multichoose-one-right.json`, all
`proved`). This lane's job was the judgement the definition lane had already
made but that this brief asked to be checked independently: **does our
`Nat.multichoose` match Mathlib's, so the `ml430` mirrors could honestly be
flipped instead of staying as separate local facts?**

**Verdict: no — confirmed by reading Mathlib's actual source, not by prose.**
Fetched `Mathlib/Data/Nat/Choose/Basic.lean` at the pinned commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f` (v4.30.0). Mathlib's `multichoose`
is a genuine three-case double recursion (Pascal-triangle style):

```lean
def multichoose : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => multichoose n (k + 1) + multichoose (n + 1) k
```

and `multichoose_eq : multichoose n k = (n + k - 1).choose k` is a **proved
theorem** about that recursion, not the definition. Our `Nat.multichoose` is
defined *directly* as that formula (`choose (pred (add n k)) k`) — i.e. we
define as a body what Mathlib proves as a theorem about a structurally
different function. This is the same shape as the `Nat.log`/`sqrt`/`clog`
caution the brief pointed at (fuel/formula construction vs. Mathlib's own
recursion), not the "literally the same function" case — so the "never flip
a mirror when the construction differs" rule was necessary here, and the
definition lane's decision (recorded in the three local facts' `notes`) was
correct. All three `ml430` facts remain `epistemic_status: open`, untouched
— per the log/sqrt precedent (`F-ml430-nat-log-le-self-da387172.json`), a
declined mirror keeps its original boilerplate `notes`, and the reasoning
lives in the paired local fact instead.

The statement TEXT does match exactly (`Nat.multichoose_zero_right`,
`_one`, `_one_right` — same names, same universally-quantified shape,
verified against `formal.statement` in each `ml430` JSON and each theorem's
`Kernel::render_lean`'d type), so the boundary values are the same and both
libraries' theorems are true of both functions. What differs is the function
symbol they are about, which is exactly what "flip" would misrepresent.

Verification run: `cargo test -p axeyum-lean-kernel --lib nat_prelude` — 117
passed, 0 failed (includes `the_build_is_deterministic`, pinned at
`85 + 429`, unchanged; `every_nat_declaration_is_checked_and_axiom_free`;
`multichoose_evaluates_correctly`). `cargo fmt --all --check` clean. No
source files touched by this lane — the definition and the three theorems
were already complete and correct.

**Skipped, as instructed:** `F:ml430-mutation-edb05acf07d9ef3f9f8232fc`
(`n.choose n = 0`, false — `choose_self` proves it is 1).

**Budget-permitting factorial bridge: not attempted.** No `ml430` fact names
a multichoose-in-terms-of-factorial identity to close (searched
`artifacts/facts/*multichoose*factorial*` and `*ml430*multichoose*` —
only the three zero-right/one/one-right mirrors exist), so there was no
concrete target to hang new proof work on without manufacturing a fact that
was not asked for.

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-multichoose-facts | Confirmed (via Mathlib source at the pinned commit) that our `Nat.multichoose` is a formula-based definition while Mathlib's is a genuine double recursion, so the three `ml430` multichoose mirror facts correctly stay `open`; no code or fact changes needed, all three theorems and their local facts were already proved by the prior lane. |
