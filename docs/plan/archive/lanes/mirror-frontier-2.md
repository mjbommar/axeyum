# Lane: mirror-frontier-2

<!-- plan-section: lane-status -->

Status: complete (2026-08-31). Four `natural-fibonacci-basic` mirrors closed,
three new declarations, ADR-0840's Mathlib-side claim corrected at the source.

## What this lane did

`check-dispatchable-frontier.py --json` at the start of this lane reported
**24 dispatchable**, not the 24 a handoff asserted — it was re-derived, and the
Fibonacci family was picked because it shares one piece of machinery
(`Nat.fib`) across four rows and one of them was already in the environment.

- `crates/axeyum-lean-kernel/src/nat_prelude/fib_extra.rs` (new) declares
  `Nat.fib_one`, `Nat.fib_two` and `Nat.fib_lt_fib_succ`, all axiom-free.
- `crates/axeyum-lean-kernel/src/nat_prelude/fib_extra_tests.rs` (new) carries
  their instantiation tests plus a first instantiation test for the
  pre-existing `Nat.fib_add`.
- Four facts flipped `open -> proved`, `proof_route: kernel-lean`,
  `axiom_footprint: []`.

Measured: `cargo test -p axeyum-lean-kernel --lib nat_prelude::` **312 passed,
0 failed** (308 before this lane). `validate-facts.py` 2497 checked, 0 errors,
`open` 237 -> **233**. Dispatchable frontier **24 -> 20**, open mirrors
**232 -> 228**. `check-autogenesis-holdout-isolation.py`
`held_out=186 settled=0 references=0 PASS` **before and after** — all four
facts are partition `development`, read from
`artifacts/autogenesis/nursery-v2-extension.json`, not inferred from a count.
`check-shape-duplicates.py` unchanged at 15 allowlisted groups, so none of the
three new declarations re-derives an existing proposition.

## The correction: ADR-0840's point 4 was wrong about Mathlib

ADR-0840 concluded that `Nat.fib` is "a second, independently divergent
construction" against "Mathlib's own two-step `Nat.rec`/well-founded
recurrence", and it says so in CLAUDE.md's Gotchas. Read at the pinned commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`,
`Mathlib/Data/Nat/Fib/Basic.lean:57` is

```lean
def fib (n : ℕ) : ℕ := ((fun p : ℕ × ℕ => (p.snd, p.fst + p.snd))^[n] (0, 1)).fst
```

— an accumulator-PAIR iteration seeded at `(0, 1)`, chosen (its own doc comment
says so) for performance over "the naive recursive implementation". Ours is
`fib n := fibAux n 0 1` with `fibAux (succ i) a b ≡ fibAux i b (add a b)`: the
same algorithm from the same seed, curried across two argument slots because
this kernel has no tuple type. Same function, different representation of the
pair, so the mirror is our statement and the flip is honest.

`fib_zero`, `fib_one` and `fib_two` are proved `rfl` in Mathlib
(`Basic.lean:61-69`) — definitional on its side exactly as here, which is the
Stirling precedent verbatim.

Note the asymmetry that made this survive: ADR-0840's points 1-3 each cite the
pinned Mathlib source, and point 4 cites only **this repository's own module
doc**. The `Nat.fastFib` half of that ADR is unaffected and still stands
(`fastFib` is a registered divergence; `Nat.fib` is not, and the divergence
registry already agreed with this reading).

## The mutation probe, including the mutant that survived

Three outcomes were sought; two were reached, in my own worktree, restored
immediately.

| mutant | outcome |
| --- | --- |
| `fib_two` restated as `Eq (fib 3) 1` | **REJECTED** — `add_declaration` refuses; the whole nat prelude fails to build, so every `fib_extra` test dies |
| `fib_one` restated as `Eq (fib 2) 1` | **ADMITTED, TRUE, AND NOT THE THEOREM** — the unit test passes unchanged |

The second is the third outcome the standard warns about, and it is not an
oversight in the test: `Eq (fib 1) 1` and `Eq (fib 2) 1` both REDUCE to
`Eq 1 1`, so **no `def_eq` check can separate them**, and going symbolic does
not help because there is no variable to generalize. Per the standard, a second
probe was designed rather than a clean bill reported: the **rendered
(unreduced) kernel type**, which is what each fact's `checker_command` matches.
Under the mutant `nat_theorem_inventory` prints
`AxNat.fib (AxNat.succ (AxNat.succ AxNat.zero))` where the true declaration
prints `AxNat.fib (AxNat.succ AxNat.zero)`, so the ledger checker kills it and
the unit test cannot. Both facts' evidence rows say this in `supports`.

Each of the four `checker_command`s was then run **verbatim** (exit 0) beside a
negative control with the pinned type corrupted (exit 1) — 8 runs, all as
expected. The exit status demonstrably depends on the finding.

## What each control rules out, and what it does not

- **`fib_one`/`fib_two`.** Rules out: the declaration existing with a wrong
  value; `def_eq` being vacuously true on small numerals (two independent
  controls, `fib 3 ≠ 1` and `fib 2 ≠ 2`). Does NOT rule out: confusing the two
  statements with each other — mechanism 1, unfixable by going symbolic, and
  covered by the rendered-type checker instead.
- **`fib_lt_fib_succ`.** Rules out: the transposed inequality (not vacuous — at
  `n = 2` it reads `2 < 1`); the hypothesis being decoration, demonstrated
  numerically since `fib 1 = fib 2 = 1` makes the unconditional form claim
  `1 < 1`. Does NOT rule out: that `2` is the sharpest threshold in some
  stronger sense, nor that the proof might route through something stronger
  than `fib_lt_fib`.
- **`fib_add`.** The symbolic check over free `m`/`n` is the discriminating
  one; a symbolic negative control rejects `... + fib m * fib (succ n)`. The
  concrete point `(3,4)` confirms `fib 8 = 21 = 2*3 + 3*5` but does NOT
  separate the product orderings — at `(3,4)` the transposed order also
  evaluates to 21. That limitation is written into the test's own doc comment.

## What stays open, and why

**The six `Int.fib` mirrors** (`int-fib-zero/one/two/neg-one/neg-two` and
`int-fib-two-mul-add-one-eq-natfib-natabs`) are dispatchable and were assessed,
not attempted. They are not blocked by a divergence — five of the six are `rfl`
in Mathlib, the same shape this lane just closed on the `Nat` side. They are
blocked by a **missing construction**: Mathlib's

```lean
def fib (n : ℤ) : ℤ :=
  if 0 ≤ n then n.toNat.fib else if Even n then -(-n).toNat.fib else (-n).toNat.fib
```

needs `Int.toNat` and two decidable branches. Measured in-tree: the Int prelude
has `Int.natAbs`, `Int.even` and `Int.odd`, and it has **no `Int.toNat`** and
**zero** uses of `Decidable` anywhere in `int_prelude.rs`. So the next lane on
this family builds `Int.toNat` plus a decidable `0 ≤ n` first; that is ordinary
work, and this is a sizing rather than a blocker claim.

## What I nearly rebuilt

`nat_prelude_tests::fib_reduces_on_numerals_with_a_negative_control` already
evaluates `Nat.fib` at `n = 0..10` against `0,1,1,2,3,5,8,13,21,34,55` with two
independent wrong-numeral controls. That is the evaluation control the new
module would otherwise have duplicated; `fib_extra_tests.rs`'s module doc cites
it and deliberately does not repeat it.

## Landed changes

| what | where |
| --- | --- |
| `Nat.fib_one`, `Nat.fib_two`, `Nat.fib_lt_fib_succ` | `crates/axeyum-lean-kernel/src/nat_prelude/fib_extra.rs` |
| their tests + first `Nat.fib_add` instantiation | `crates/axeyum-lean-kernel/src/nat_prelude/fib_extra_tests.rs` |
| prelude wiring, name registry, coverage list | `crates/axeyum-lean-kernel/src/nat_prelude.rs`, `.../nat_prelude_tests.rs` |
| four mirrors flipped to `proved` | `artifacts/facts/F-ml430-nat-fib-{one,two,lt-fib-succ,add}-*.json` |

No ADR was written: the mirror-flip criterion this lane applied is already
recorded, and the correction to ADR-0840's point 4 is a factual repair of an
existing decision rather than a new one. It is stated in `fib_extra.rs`'s module
doc, in each fact's `provenance.established_by`, and here.
