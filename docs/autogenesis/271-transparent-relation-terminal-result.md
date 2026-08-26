# Transparent relation terminal result

Date: 2026-08-26

## Result

The bounded-induction producer no longer classifies a proposition-valued
transparent relation as non-equality before checking what it reduces to. After
the exact `Eq` fast path declines, it weak-head-normalizes the terminal goal
once and admits the equality grammar only when the result is an exact `Eq`
application. The proof still has to infer against the original proposition.

This is target-agnostic and independently controlled. A synthetic transparent
wrapper around `Eq n n` produces an axiom-free admitted proof; the same wrapper
around the false proposition `∀ n, n = 0` declines.

A separate full-population control ran the existing no-premise ModEq-family
producer instead of retrieved induction. It accepted 0/51, declined all 24
importable rows as `TerminalNotClosed`, rejected the same 27 statement
closures, and accepted no false control. Its byte-identical result is
[`open-modeq-family-census-v1.json`](../../artifacts/autogenesis/open-modeq-family-census-v1.json)
(SHA-256 `d5cdd004e8f61935da71b36ff2bead25f787db7fbd67c6cace4570aba51bcac8`).
So orchestration was not the whole gap: the existing relation producer only
closes reflexivity/symmetry/transitivity shapes and receives no arithmetic
premises.

The held-out-safe focused census freezes the 13 positive goals previously
classified as `non-equality-terminal-family` plus all six false controls. Two
independent runs produced byte-identical
[`non-equality-retrieved-induction-census-v1.json`](../../artifacts/autogenesis/non-equality-retrieved-induction-census-v1.json)
with SHA-256
`6a0d5b39ad55c934570b2bd4e1fb3de73b852a0c23109dd01aff0f5a31182f93`.

| Outcome | Rows |
|---|---:|
| Accepted | 0 |
| Declined after search | 17 |
| Statement import rejected | 2 controls |
| False controls accepted | 0 |

For the 13 positives, all ten `Nat.ModEq`/`Int.ModEq` terminals now reach the
equality proof-composition stage and decline as
`TerminalNotDefEqNoRewrite`. The three factorial `Dvd`/`Not` propositions
remain correctly `NotEqualityGoal`. This is a real stage-boundary improvement,
not theorem production.

## What remains missing

The current ranking supplies relation-level congruence lemmas such as the
native `Nat.mod_eq_add_left`, but retrieved equality rewriting consumes
equality theorems. A first reading suggested this native chain:

```text
Nat.dvd_refl n
    -> Nat.mod_eq_zero_of_dvd n n
    -> Nat.ModEq n n 0
```

Both supporting theorems are already axiom-free in the kernel, but neither the
current ranking nor the equality-only rewrite stage assembles this application
chain. More importantly, that chain is **not** a proof of the imported target:
Axeyum's native lowercase `Nat.modEq` is an existential congruence relation,
while imported Mathlib `Nat.ModEq` unfolds to equality of remainders. The two
must not be conflated.

The bounded application producer should retain the native chain as a typed
composition control. The actual imported path starts with checked remainder
equalities, first `Nat.mod_self : ∀ n, mod n n = 0`, and then reusable
modulo-add equations. Retrieved equality rewriting can consume those contracts
without an unsound relation transport. At least three siblings must convert
under the unchanged operation before it earns production authority.

The first foundation increment now constructs that native `Nat.mod_self`
axiom-free and retrieves it first from the visible statement's alpha-stable
shape. Fresh transport still declines: its successor proof uses Axeyum's
executable-division specification, whose proof is tied to Axeyum's native
`Nat.mod` implementation and does not type-check over imported Mathlib
`Nat.mod`. This is useful negative evidence. The next step is not to label the
types compatible; it is to reconstruct a target-local remainder proof from the
imported definition and portable order facts, or build an independently
checked semantic bridge. Until that succeeds, production credit stays zero.

The two runs also measured 184 transported candidates added, 67 already in the
capsules, and 89 typed transport declines. The expensive transport denominator
remains separate from the proof-plan decline.

Run `just autogenesis-non-equality-terminal-census` on a host with the external
capsule mount. The artifact is measurement-only and grants no operation or
fact-transition authority.
