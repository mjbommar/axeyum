# ADR-1579: `List` is an ordinary inductive — no quotient needed, unlike the concession that blocked it

Date: 2026-09-03
Status: Accepted
Lane: `list-carrier-1`

Index-summary: Three concessions in the dominance document trace to one
missing data structure — "no `List`, no `Finset`, no polymorphic `Prod`".
ADR-1520 (`Nat.Multiset`) and ADR-1577 (`Nat.Finset`) each closed a piece by
COMPUTING a ℕ-only carrier (a function-plus-bound pair) specifically to avoid
the permutation quotient a real `List` would otherwise cost. `List` is the
third piece, and it needs no quotient at all: nothing about it claims two
permutations of the same elements are equal, so there is nothing to quotient
by. `List.{u} : Type u → Type u` (`nil`/`cons`) is declared here as an
ordinary universe-polymorphic inductive, admitted through the same trusted
`add_inductive` gate as `Nat`/`Bool`/`Exists`/`Acc`, instantiated at `u := 0`
for every operation and theorem. `length`, `append` (recursing on its FIRST
argument), `map`, `foldr`, `reverse` land as `Definition`s via `List.rec`;
`append_assoc`, `append_nil`, `reverse_append`, `reverse_reverse`,
`length_map`, `foldr_append` land as theorems needing nothing beyond `List`
and `Eq`; `sum`, `length_append`, `sum_append`, `length_reverse`,
`List.toMultiset`, `List.count` land in a separate `List`/`Nat` bridge that
needs the real named `Nat.add` (declared after `List` in the prelude chain).
`Kernel::axiom_footprint` is `[]` for every one of the nine theorems, read
from the kernel, not asserted. `List.count_toMultiset` — the theorem tying
the new inductive carrier to `Nat.Multiset`'s function-plus-bound one — did
NOT land; the obstruction is measured and recorded below, not guessed.

## Context

ADR-1310 (2026-08-31) decided **not** to add `List`, on the ground that every
use cited as needing it — a permutation-summing route, a Cauchy–Binet
expansion, a Leibniz determinant sum — actually only needed a **fold** over a
finite index set, which `Int.sumMaps` already gave without an aggregate. That
finding is not revisited here: nothing in ADR-1310's `sumMaps` argument was
wrong, and this ADR does not reopen it. ADR-1310 also measured `Nat.Fin`
(an indexed finite type declared 2026-08-23) at **zero non-test consumers**
and named that the prior for how an aggregate mechanism goes when it lands
ahead of a real use.

What changed since is ADR-1520 and ADR-1577. Both landed a ℕ-only **computed**
carrier — `Nat.Multiset` (`mk : (Nat → Nat) → Nat → Multiset`) and
`Nat.Finset` (`mk : (Nat → Bool) → Nat → Finset`) — specifically to state
uniqueness-of-factorization and finite-set arguments **without** the
permutation quotient Mathlib's `List`-backed `Multiset`/`Finset` would cost.
Both ADRs are explicit that this is a workaround for a missing `List`, not a
replacement for one: ADR-1520 records "Add `List` and a permutation quotient…
is a much larger change" as an alternative considered and declined **for that
specific proof**, not as a permanent verdict on `List` itself. ADR-1495
(the constructor-field universe guard) separately measured, on 2026-09-01,
that `List.{u} Char` at both `u := 0` and `u := 1` already exists as a real,
Lean-legal declaration in `tests/support/lean_shaped_string.rs` and
`tests/mutual_inductive_groups.rs` — as test-only scaffolding for the
string-literal bootstrap and inductive-admission fuzzing, never as prelude
surface.

So the situation this ADR closes is: a `List`-shaped fixture already exists
and is exercised by the kernel's own test suite, two sibling carriers already
exist specifically because a real `List` was judged too expensive for their
one proof each, and the dominance document still concedes "no `List`" as a
structural gap. This lane asks the question ADR-1310 answered narrowly — "is
`List` worth adding" — again, but for `List` **on its own terms** rather than
as a vehicle for one hard proof, with the Multiset/Finset bridge as the
adoption path ADR-1310's "zero consumers" prior explicitly asks for before a
mechanism lands.

## Decision

**Add `List` as an ordinary inductive.** It costs no axioms, needs no
quotient, and the two ℕ-only carriers it would otherwise duplicate
(`Nat.Multiset`, `Nat.Finset`) are exactly the reason the string-literal
fixture already builds this shape — this lane is the first to promote it from
test scaffolding to prelude surface.

### The universe

```text
inductive List.{u} (α : Type u) : Type u
  | nil  : List α
  | cons : α → List α → List α
```

`α : Type u = Sort (u+1)` is a constructor field, and the family's own result
universe is also `Sort (u+1)` (`List.{u} α : Type u`) — the field sits **at,
not above**, the result universe, so ADR-1495's guard
(`KernelError::ConstructorFieldUniverseTooBig`) accepts it, exactly as it
accepts the identical shape in the string-literal fixture. Every operation
and theorem in this prelude fixes `u := 0` (`List.{0} α` for `α : Type 0`,
matching `Nat : Type 0`), so nothing downstream reasons about `u`
symbolically — but the inductive itself stays genuinely universe-polymorphic;
a later consumer needing `List.{1}` (a list of `Prop`-quantified
propositions, say) is not blocked by this module's own choice to specialize.

### What landed, and where

`List` sits **before** `nat` in the prelude chain: `build_list_prelude`
depends only on `build_logic_prelude` (`List Nat` needs the `Nat` *type*, an
ordinary inductive already in the logic prelude, not `Nat`'s arithmetic).

| where | what | needs |
| --- | --- | --- |
| `list_prelude.rs`/`ops.rs` | `List`, `length`, `append`, `map`, `foldr`, `reverse` | `build_logic_prelude` only |
| `theorems.rs` | `append_assoc`, `append_nil`, `reverse_append`, `reverse_reverse`, `length_map`, `foldr_append` | `build_logic_prelude` only |
| `bridge.rs` (`build_list_nat_bridge`) | `sum`, `length_append`, `length_reverse`, `sum_append`, `toMultiset`, `count` | `build_nat_prelude` (`Nat.add` and its theorems, `Nat.Multiset`) |

`sum`/`length_append`/`sum_append`/`length_reverse` cannot live beside the
other operations for a structural reason, not a stylistic one: this
prelude's own `Nat.add` recurses on its RIGHT argument, so `0 + x` and
`succ a + x` do not reduce for a symbolic `x` by defeq alone —
`zero_add`/`succ_add`/`add_assoc` are real theorems, and reinventing them
inline (as `sum` alone would need to, if declared before `nat`) would
duplicate what `nat_prelude` already proves. `toMultiset`/`count` are
similarly bridge-only because they mention `Nat.Multiset`.

Every `Definition` is exercised at concrete, small, discriminating arguments
with a negative control a plausible wrong implementation would fail
(`length [1,2,3] = 3` not `2`; `append [1] [2,3] = [1,2,3]` not
`[2,3,1]`; `reverse [1,2,3] = [3,2,1]` not the identity; `map succ [0,1] =
[1,2]` not unchanged; `sum [1,2,3] = 6` not `3`; `toMultiset [2,2,3]` has
`Multiset.count _ 2 = 2` not `1`), per this repository's own rule that the
trusted gate cannot tell a `Definition` computing the wrong value from a
correct one.

### The proof machinery: carrier-generic, not a new hardcoded dev layer

`Nat.rec`-based proof construction in this prelude has historically gone
through a per-carrier hardcoded layer (`NatOps`, `IntDev`) — CLAUDE.md's own
gotchas record three separate lanes bitten by a cross-carrier use failing as
one opaque `TypeMismatch` in one day. This module does not add a fourth. It
reuses ADR-1495's G4 pilot 2 finding — that a carrier-generic `congr_arg`
(explicit `(ty, level)` parameters instead of a hardcoded `nat_ty()`) is a
drop-in replacement for `NatOps::congr` — and generalizes it into
`eq_of`/`refl_of`/`symm_of`/`trans_of`/`congr_of` (`list_prelude/ops.rs`),
parameterized by the carrier's own `(ExprId, LevelId)` pair. The same five
functions build every theorem in this module over `List α`, `Nat`, or `β`
(an arbitrary `Type 0` carrier a fold's codomain is instantiated at) with no
per-carrier duplication. `list_induct_prop` (also `ops.rs`) is the one
`List.rec`-with-`Prop`-motive induction helper every theorem's proof runs
through.

### Two bugs the kernel caught, both from this repository's own playbook

**Every `Eq`/congruence call was first built at the wrong universe level.**
`List.rec`'s Prop-motive elimination level (`Sort 0`) and the CARRIER's own
sort (`Sort 1`, since `List.{0} α : Type 0 = Sort 1`, same as `Nat`) are two
different numbers that happen to share a name (`zero_lvl` was in scope for
both), and the first draft used the recursor's motive level for the `Eq`
carrier level everywhere. The kernel's rejection was exactly
`kernel-proof-engineering.md`'s documented shape — `TypeMismatch { expected:
ExprId(0), got: ExprId(2) }`, a tiny `expected` id meaning the kernel wanted
a SORT, not that two ordinary types disagreed — and it fired on the very
first theorem attempted (`append_assoc`).

**`reverse_append`'s base case had a direction swapped into `symm_of`
backwards.** `append_nil(α, l) : Eq (append l nil) l` — the equation reads
right-to-left relative to what the base case needs — and `symm_of`'s
contract is `h : Eq ty a b ⊢ Eq ty b a`; the first draft passed `(a, b)` in
the GOAL's direction rather than `h`'s actual direction. This is exactly the
family CLAUDE.md's own gotchas name repeatedly ("`x`/`x'` backwards is the
single most common bug in this development") and it fired the same way, as
an opaque `TypeMismatch` requiring `Kernel::infer` + `render_lean` on the
constructed VALUE (not just the declared type) to localize, per the same
document's own recommended technique.

Both were found and fixed by the method the linked document prescribes:
bisecting to the failing declaration by instrumenting each theorem in
sequence, then rendering the declared type against `kernel.infer(value)`'s
actual inferred type side by side.

## What did NOT land, and the measurement

**`List.count_toMultiset : ∀ a l, count a l = Nat.Multiset.count (toMultiset
l) a`.** The `nil` case is immediate (`Nat.Multiset.count_eq_zero_of_bound_le`
plus `Nat.zero_le`). The `cons` case needs a genuine case split on
`Nat.beq head a` — the same test `List.count`'s own fold already performs —
and, in the `false` branch, a bridge lemma from `Nat.beq head a = false` to
`head ≠ a` to invoke `Nat.Multiset.count_singleton_of_ne`. That bridge lemma
was not located or built by this lane; `declare_count_to_multiset` in
`bridge.rs` is written to attempt it and deliberately returns `Err` (the
caller's `.ok()` then makes `ListNatBridge::count_to_multiset` `None`) rather
than shipping a stub that looks landed. A future lane picking this up should
start from `Nat.beq_eq_true_iff`/`Nat.eq_of_beq_eq_true` (this prelude's
existing `beq`↔`Eq` bridge) and the case-split idiom `nat_prelude`'s own
`Bool.rec`-based selectors use elsewhere, rather than re-deriving one.

**`List.Perm` and `perm_reverse`.** Not attempted; the brief marked this
"if time remains" and it did not.

## What this carrier deliberately does not provide

- **No `foldl`, no `nth`.** Neither is needed by any landed theorem
  (`length_append`, `append_assoc`, `append_nil`, `reverse_reverse`,
  `length_map`, `foldr_append`, `sum_append`, `length_reverse` all reach
  through `length`/`append`/`map`/`foldr`/`reverse`/`sum` alone), and adding
  either was deprioritized in favor of landing the theorem list and the
  bridge within this lane's scope. `foldl` is genuinely a harder
  construction here — it needs the "fold as a function, apply at the end"
  encoding (`foldl f z l := (List.rec … ) z` with a `β → β`-valued motive)
  rather than a direct constant-motive fold — and `nth` needs a nested
  `Nat.rec` inside `List.rec`'s cons case. Both are ordinary work on top of
  this module, not a kernel question.
- **No extensional equality of lists**, and no `List.beq`. Nothing here
  needed a decidable equality test on lists themselves (only on their
  `Nat`-typed elements, via `Nat.beq`, inside `List.count`).
- **No polymorphism beyond `Type 0`.** The inductive is genuinely
  `List.{u}`, but every declared operation and theorem fixes `u := 0` for
  the reasons given above (matching `Nat`, matching every other carrier this
  prelude touches). A `List.{1}` consumer is not blocked by the kernel, only
  unbuilt.
- **No process-wide prelude template.** `PreludeKey::List` falls through to
  the ordinary build path every time (`prelude_cache.rs`'s `slot()` returns
  `None`, matching `String`'s existing precedent) — its marginal cost over
  `Logic` has not been measured, unlike `Nat`/`Int`/`Real`/`CReal`, which
  each earned a template from a measured cost.

## Consequences

- `List` is a sixth non-`Prop` inductive in this prelude family (`Nat`,
  `Nat.Fin`, `Nat.Pair`, `Nat.Multiset`, `Nat.Finset`, `List`), and the
  first that is genuinely universe-polymorphic rather than ℕ-only.
- The dominance document's "no `List`" concession is now false as written
  for the operations and theorems landed here. This ADR does not edit that
  document; whoever next revises it should read this ADR and the facts it
  registers.
- ADR-1310's own decision — no aggregate type, keep the function-plus-bound
  idiom, revisit if a genuinely order-sensitive statement becomes the
  priority — is not overturned. `List` lands here because ADR-1520 and
  ADR-1577 are the adopters ADR-1310's "abandonment condition" (a mechanism
  with zero non-test consumers should not have landed) was written to guard
  against, and `List.toMultiset`/`List.count` demonstrate a real cross-carrier
  use, even though `count_toMultiset` itself did not land. `Nat.Fin`'s prior
  (zero non-test consumers) is unchanged and this ADR does not touch it.
- `Nat.Multiset` and `Nat.Finset` are unaffected: neither is redefined,
  neither loses a theorem, and neither gains a dependency on `List`. The
  bridge is additive.

## Alternatives considered

- **Represent `List` as a `Nat`-indexed function plus a length**, matching
  ADR-1310's function-plus-bound idiom exactly. Rejected: this is precisely
  the representation `Nat.Multiset`/`Nat.Finset` already use for their own
  purposes, and duplicating it for `List` buys nothing an ordinary inductive
  does not already give for free — the whole point of this ADR is that a real
  `List` costs zero axioms here, unlike Mathlib's quotiented one.
- **Land `List.count_toMultiset` by brute-force case analysis rather than
  finding the `beq`-to-`ne` bridge lemma.** Not attempted; a proof that
  cannot cleanly discharge the `false` branch is exactly the shape of defect
  this repository's own evidence-and-checker-discipline note warns against
  landing under time pressure — better to record the sized negative than
  ship a proof built to fit rather than to hold.

## Evidence

| what | where |
| --- | --- |
| the inductive, `length`/`append`/`map`/`foldr`/`reverse` | `crates/axeyum-lean-kernel/src/list_prelude.rs`, `list_prelude/ops.rs` |
| the six pure-`List` theorems | `crates/axeyum-lean-kernel/src/list_prelude/theorems.rs` |
| the `List`/`Nat` bridge | `crates/axeyum-lean-kernel/src/list_prelude/bridge.rs` |
| the carrier-generic `Eq` layer | `crates/axeyum-lean-kernel/src/list_prelude/ops.rs` (`eq_of`/`refl_of`/`symm_of`/`trans_of`/`congr_of`/`list_induct_prop`) |
| evaluation tests with negative controls | `crates/axeyum-lean-kernel/src/list_prelude/list_prelude_tests.rs`, `list_prelude/bridge/bridge_tests.rs` |
| the string-literal fixture's prior `List.{u}` shape | `crates/axeyum-lean-kernel/tests/support/lean_shaped_string.rs` |
| the universe guard this inductive is checked against | ADR-1495 |
| the two ℕ-only computed carriers this bridges to | ADR-1520 (`Nat.Multiset`), ADR-1577 (`Nat.Finset`) |
| the prior decision this narrows, not overturns | ADR-1310 |

Verification: `cargo test -p axeyum-lean-kernel --lib -- list_prelude::` —
17 passed (10 in the declarations commit, 7 in the bridge commit — see
lane status for exact counts); `cargo test -p axeyum-lean-kernel --lib --
nat_prelude::` — 422 passed, confirming no regression;
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` clean.
Axiom footprint for all nine theorems (`append_assoc`, `append_nil`,
`reverse_append`, `reverse_reverse`, `length_map`, `foldr_append`,
`length_append`, `length_reverse`, `sum_append`) read from
`Kernel::axiom_footprint` via the tests' own coverage checks, not asserted
from a list. **Not run:** the full workspace `--lib`/`--tests` sweep,
`cargo deny check`, `just foundational-resources`.
