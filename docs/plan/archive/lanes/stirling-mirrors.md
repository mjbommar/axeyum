# Lane: stirling-mirrors — close the `Nat` Stirling-number mirror family

<!-- plan-section: lane-status -->

**Done (`DONE`, stirling-mirrors, 2026-08-31).** Ten `ml430` mirrors closed —
the whole `Mathlib.Combinatorics.Enumerative.Stirling` family — with ten
theorems admitted through `Kernel::add_declaration` on the **first attempt**,
every one axiom-free.

**Selected from the live frontier, not from a handoff.**
`python3 scripts/check-dispatchable-frontier.py --json` at lane start: exit 0,
**14 dispatchable**, 166 held-out, 12 mutation controls, 11 blocked. Ten of the
14 were the Stirling family, which `nat_prelude/stirling.rs` had declared as
definitions with — per ADR-0653 — no theorem about either. After this lane the
frontier reports **4 dispatchable** (`fermat-primefactors-one-lt`,
`size-bit`, `size-le-size`, `squarefree-ext-iff`).

**Held-out isolation, before and after:** `held_out=166 settled=0 PASS` both
times. All ten are `train` in `nursery-v2-extension.json` (checked in the
manifest before declaring, not after), and no supporting theorem was declared
alongside them — the module declares exactly the ten mirrors and nothing else,
so there is no ADR-0645 contamination surface.

## The honesty question

The criterion is the def-vs-theorem one, checked at Mathlib's own source at the
pinned commit `c5ea00351c28e24afc9f0f84379aa41082b1188f` rather than from a
paraphrase — `Mathlib/Combinatorics/Enumerative/Stirling.lean`:

| site | content |
| --- | --- |
| `:51` | `def stirlingFirst \| 0,0 => 1 \| 0,_+1 => 0 \| _+1,0 => 0 \| n+1,k+1 => n * stirlingFirst n (k+1) + stirlingFirst n k` |
| `:113` | `def stirlingSecond` — identical but the coefficient is `k+1` |
| `:58`, `:62`, `:66`, `:82` | `stirlingFirst_zero`, `_zero_succ`, `_succ_zero`, `_succ_succ`, each proved `:= rfl` |

That is `nat_prelude/stirling.rs`'s body verbatim, and the equation compiler
produces our shape for those four cases: an outer recursion on the row index
yielding a whole row, an inner one selecting the column. The strongest evidence
that these are the SAME function rather than merely extensionally equal is the
last row of that table — **Mathlib proves its own four defining equations by
`rfl`**, so they are definitional on its side exactly as on ours. This is the
opposite of `Nat.multichoose`, where our body is Mathlib's *theorem* about a
structurally different `def` and the mirrors must stay open.

The rendered types differ from the pinned surface statements only in binder
info: Mathlib marks `{n k}` implicit in the two `eq_zero_of_lt` rows.

## What landed

`crates/axeyum-lean-kernel/src/nat_prelude/stirling_lemmas.rs` (new), wired last
in `build_nat_prelude`, plus `stirling_lemmas_tests.rs` (new) and 10 entries in
`nat_prelude_tests::theorem_names`.

| fact | `Nat.…` | rendered type |
| --- | --- | --- |
| `F:ml430-nat-stirlingfirst-zero-ae5f4939` | `stirlingFirst_zero` | `Eq AxNat (stirlingFirst 0 0) (succ 0)` |
| `F:ml430-nat-stirlingfirst-zero-succ-d25889f3` | `stirlingFirst_zero_succ` | `(x0 : AxNat) -> Eq (stirlingFirst 0 (succ x0)) 0` |
| `F:ml430-nat-stirlingfirst-succ-zero-a58c6f3c` | `stirlingFirst_succ_zero` | `(x0 : AxNat) -> Eq (stirlingFirst (succ x0) 0) 0` |
| `F:ml430-nat-stirlingfirst-succ-succ-61c94738` | `stirlingFirst_succ_succ` | `(x0 x1 : AxNat) -> Eq (stirlingFirst (succ x0) (succ x1)) (add (mul x0 (stirlingFirst x0 (succ x1))) (stirlingFirst x0 x1))` |
| `F:ml430-nat-stirlingfirst-eq-zero-of-lt-6f46764f` | `stirlingFirst_eq_zero_of_lt` | `(x0 x1 : AxNat) -> lt x0 x1 -> Eq (stirlingFirst x0 x1) 0` |
| `F:ml430-nat-stirlingsecond-eq-zero-of-lt-f3caf8bd` | `stirlingSecond_eq_zero_of_lt` | `(x0 x1 : AxNat) -> lt x0 x1 -> Eq (stirlingSecond x0 x1) 0` |
| `F:ml430-nat-stirlingfirst-self-4d06a0eb` | `stirlingFirst_self` | `(x0 : AxNat) -> Eq (stirlingFirst x0 x0) (succ 0)` |
| `F:ml430-nat-stirlingfirst-one-right-84dfc371` | `stirlingFirst_one_right` | `(x0 : AxNat) -> Eq (stirlingFirst (succ x0) (succ 0)) (factorial x0)` |
| `F:ml430-nat-stirlingfirst-succ-self-left-135bbfbf` | `stirlingFirst_succ_self_left` | `(x0 : AxNat) -> Eq (stirlingFirst (succ x0) x0) (choose (succ x0) (succ (succ 0)))` |
| `F:ml430-nat-stirlingsecond-one-right-ef2ad447` | `stirlingSecond_one_right` | `(x0 : AxNat) -> Eq (stirlingSecond (succ x0) (succ 0)) (succ 0)` |

No supporting theorem was declared. Ten mirrors, ten declarations.

## What was cheap, and why

Four of the ten are `Eq.refl`. Our recursor reduces at a literal `0` or a `succ`
constructor in either position, so the recurrence holds by δβι and needs no
equation lemma — the same reason Mathlib closes them with `rfl`.

The other six route through one shape, and it already existed:
`Nat.choose_eq_zero_of_lt`'s. Induction on the row with an inner `Nat.rec` on
the column used only to expose its SHAPE (motive is the arrow `Lt _ k → _`, each
branch re-introducing its own specialized hypothesis); the `k = 0` arms are
vacuous; the `succ`/`succ` leaf strips one `succ` with `le_of_succ_le_succ` and
`le_succ_of_le` to reach the hypothesis at both columns.

`stirlingFirst_eq_zero_of_lt` and `stirlingSecond_eq_zero_of_lt` are **one
builder instantiated twice**. The triangles differ only in the recursive
column's coefficient, and that coefficient is multiplied by a zero in this
proof, so the term generator is literally identical.

Three operand orders decided the remaining cost, all of them the asymmetries
`CLAUDE.md` records:

- `Nat.add` recurses RIGHT, so `add X 0 ≡ X` and every `stirling _ (n+1) 0 ≡ 0`
  collapse is free; the `zero` from `mul_zero` always lands in the LEFT slot
  where it does not reduce, which is why the chains end on a literal rather than
  on `zero_add`.
- `Nat.mul` recurses RIGHT, so `mul c 0 ≡ 0` is free but `mul c 1` is not `c` —
  `mul_one` is a real theorem and `stirlingFirst_succ_self_left` needs it.
- **`Nat.factorial_succ` here is `factorial n * succ n`, the OPPOSITE order from
  Mathlib's.** That is the only place any of these proofs differs from Mathlib's:
  `stirlingFirst_one_right` needs one `mul_comm` that Mathlib's does not.

Nothing forms a numeral larger than `2`.

## A vacuous negative control, and it is not the shape the warnings predict

The obvious control for `stirlingFirst_zero_succ` is the transposed index
`stirlingFirst (k+1) 0 = 0` — a different-looking proposition, no numerals on
either side, apparently safe. It is vacuous: `stirlingFirst 0 (succ k)` reduces
through the ZERO row's inner recursor at a `succ` scrutinee, and
`stirlingFirst (succ k) 0` reduces through the SUCC row's inner recursor at a
literal `0`, so **both land on the literal `0` even at a free `k`** and the two
statements are one statement up to defeq.

The suite caught it, not review — the assertion failed on its first run.

What is worth carrying: **going symbolic did not rescue this control.** That is
the standard remedy (it is what rescued the min/max lane's `max 7 2`), and here
it fails, because the reduction that collapses the distinction is driven by
CONSTRUCTOR shapes rather than by numerals. The replacements drop the `succ`
instead — `stirlingFirst 0 k = 0` and `stirlingFirst n 0 = 0`, each false at `0`
and each genuinely stuck at a free variable — and the suite additionally asserts
the counterexample (`stirlingFirst 0 0 = 1`), so a control that stopped
discriminating fails rather than passes quietly.

Two more controls were considered and rejected as vacuous before being written:
the cross-kind swap for `_self` (both triangles are all ones on the diagonal)
and for `_succ_self_left` (Mathlib proves the same `choose (n+1) 2` identity for
both kinds, and both are `6` at `n = 3`). Where the kinds DO separate — column
one, `n!` against all ones — the cross-kind control is used, because it is the
strongest available.

The evidence checker's negative control is also a real theorem rather than an
invented name: the `grep -c` command exits 0 for all ten declared mirrors and
exits 1 for `stirlingSecond_self`, which Mathlib proves and this prelude does
not declare.

## `every_nat_declaration_is_checked_and_axiom_free` fired

On the first full sweep it named all ten as live in the environment but absent
from `theorem_names`, so nothing was checking their kind, determinism, or
axiom footprint. Added there. This is the environment-derived coverage
assertion working exactly as its own doc comment says it should.

## Gates run (all foreground, all complete)

| gate | result |
| --- | --- |
| `cargo test -p axeyum-lean-kernel --lib nat_prelude::` | 296 passed, 0 failed |
| `cargo test -p axeyum-lean-kernel --lib int_prelude::` | 61 passed, 0 failed |
| `cargo test -p axeyum-lean-kernel --lib nat_prelude::stirling` | 9 passed, 0 failed |
| `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` | clean |
| `python3 scripts/validate-facts.py` | 2444 facts, 0 errors |
| `python3 scripts/check-settled-fact-statements.py` | `PASS`, `drifted=0` |
| `python3 scripts/check-autogenesis-holdout-isolation.py` | `held_out=166 settled=0 PASS` |
| `python3 scripts/check-dispatchable-frontier.py` | exit 0, 4 dispatchable remain |
| `python3 scripts/check-shape-duplicates.py` | 15 groups, all allowlisted |
| `nat_axiom_inventory --require-axiom-free nat` | `nat trusted surface = 0` |
| `prelude_theorem_inventory --include-constructed` | all ten rows `nat  Nat.stirling…  0` |
| each fact's `checker_command` | 10 positives exit 0; `stirlingSecond_self` exits 1 |

`check-fact-depends-derived.py --fix` added 16 edges across 5 facts, **all of
them this lane's** — no pre-existing drift was repaired in this commit.

## Remaining dispatchable frontier (4)

`F:ml430-nat-size-bit-c601dbf0` and `F:ml430-nat-size-le-size-c4b98f53` are one
pair over `Nat.size`; `F:ml430-nat-fermat-primefactors-one-lt-58343c6f` and
`F:ml430-nat-squarefree-ext-iff-7218327d` are singletons. Nothing here is a
ten-row family any more, so the next lane should expect to justify a smaller
batch — or the queue needs a refill rather than another sweep.
