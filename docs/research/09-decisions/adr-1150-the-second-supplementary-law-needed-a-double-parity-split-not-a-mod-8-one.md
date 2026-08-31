# ADR-1150: The second supplementary law needed a double parity split, not a `mod 8` one

Status: accepted
Date: 2026-08-31
Index-summary: **The second supplementary law of quadratic reciprocity is
proved, axiom-free, in this kernel**: `Int.secondSupplementaryLaw` classifies
`2^((p-1)/2) mod p` by `p mod 8` for an odd prime `p = 2m+1` -- `+1` exactly
when `p = 8q+1` or `8q+7`, `-1` exactly when `p = 8q+3` or `8q+5`. Three
declarations, all admitted on the FIRST attempt, all with an empty
`axiom_footprint`. ADR-1130's handoff recorded it as blocked on "a `p mod 8`
case split" that did not exist -- and could not have been used if built, since
`Nat.div`/`Nat.mod` are stuck at a symbolic argument, so a mod-8 HYPOTHESIS
cannot be evaluated. What the proof needs runs the other way: `Nat.even_or_odd`
PRODUCES the shape with a computed half, and applying it twice (at `m`, then at
`div m 2`) hands over all four classes with no division ever reducing. Nothing
was re-derived: the two `(-1)^n` sign lemmas were private helpers inside
`int_prelude/fibonacci.rs` and were exposed rather than rebuilt, and
coprimality of the multiplier is not a hypothesis at all because
`Nat.coprime_two_left` already existed. This does NOT establish the classical
`IsQuadraticResidue` form -- that still needs the converse of Euler's
criterion, and `qr_criterion.rs`'s recorded gap is unchanged.

Lane: `second-supplementary-law`

## Context

[ADR-1130](adr-1130-gauss-lemma-closes-and-the-handoffs-remaining-blockers-were-not-needed.md)
landed **Gauss's lemma**, `Int.gaussLemmaSignCount`:

```text
∀ m a, Nat.PrimeCond (2m+1) → gcd a (2m+1) = 1 →
  a^m ≡ (−1)^(gaussNegCount (2m+1) a m)   (mod 2m+1)
```

and `Nat.gaussNegCountTwoClosedForm` already evaluated that count at `a := 2`:

```text
∀ m, gaussNegCount (succ (mul 2 m)) 2 m = sub m (div m 2)
```

So `2^m mod p` was reduced to the parity of `m − ⌊m/2⌋`. ADR-1130's handoff
recorded the remaining gap as **"a `p mod 8` case split over that closed form"**
and noted that no such split existed in `nat_prelude/`.

## Decision

Land the law in its **Legendre-symbol (power-residue) form**, with the residue
class stated **structurally** rather than through a `mod 8` term.

`Int.secondSupplementaryLaw : ∀ m, Nat.PrimeCond (succ (mul 2 m)) →`

```text
Or (And (Or (m = 4q)   (m = 4q+3)) (ModEq p (2^m)  1))
   (And (Or (m = 4q+1) (m = 4q+2)) (ModEq p (2^m) −1))
```

with `q := div (div m 2) 2`, `p := 2m+1`, and the four shapes written out as
`add`/`succ` terms. At `p = 2m+1` those are `p = 8q+1, 8q+3, 8q+5, 8q+7`, so the
left disjunct is exactly `p ≡ ±1 (mod 8)`. The four shapes are exhaustive and
pairwise distinct, so the single disjunction gives **both directions of each
line** — no separate converse is needed.

Three new declarations, all admitted axiom-free on the first attempt:

| declaration | statement |
| --- | --- |
| `Nat.half_ceil_parity` | the parity of `sub m (div m 2)` is decided by `m mod 4` |
| `Int.pow_neg_one_of_even` | `Nat.Even n → (−1)^n = 1` |
| `Int.pow_neg_one_of_odd` | `Nat.Odd n → (−1)^n = −1` |

## The handoff's blocker did not exist, and could not have

A `mod 8` (or `mod 4`) **hypothesis** is not usable in this kernel:
`Nat.div`/`Nat.mod` are stuck at a symbolic argument, so a proof handed
`mod m 4 = 1` would first have to reconstruct `m`'s shape from it. Building the
"missing" mod-8 machinery would have produced a lemma the proof could not
consume.

What works runs the other way round. `Nat.even_or_odd` **produces** the shape,
with the half **computed**:

```text
∀ n, Or (n = add (div n 2) (div n 2)) (n = succ (add (div n 2) (div n 2)))
```

Applying it twice — at `m`, then at `h := div m 2` with `q := div h 2` — hands
over all four classes with no division ever needing to reduce:

| `m` | `h` | `m` in terms of `q` | `N = m − h` | parity |
| --- | --- | --- | --- | --- |
| `h+h` | `q+q` | `(q+q)+(q+q)` | `q+q` | even |
| `succ (h+h)` | `q+q` | `succ ((q+q)+(q+q))` | `succ (q+q)` | odd |
| `h+h` | `succ (q+q)` | `succ(q+q) + succ(q+q)` | `succ (q+q)` | odd |
| `succ (h+h)` | `succ (q+q)` | `succ (succ(q+q)+succ(q+q))` | `succ (succ (q+q))` | even |

Both `N` evaluations are one application of `Nat.add_sub_cancel_left`
(`sub (add x y) x = y`). The odd-`m` one is the instructive half: at
`(x, y) := (h, succ h)` the lemma's own left-hand side is
`sub (add h (succ h)) h`, and `add h (succ h)` is **definitionally**
`succ (add h h)` because `Nat.add` recurses on its right argument. Keeping the
symbolic side on the LEFT throughout the file is what makes that free — the
standing operand-order rule, paying off rather than biting.

Only the fourth row needs a real lemma: `succ (succ (q+q))` is
`add (succ q) (succ q)` only up to `succ_double_eq`.

This is the **third** consecutive instance of the standing rule that *a
handoff's report of what it LANDED is reliable and its report of what REMAINS
is a hypothesis* — and it is the sharper variant, because the named blocker was
not merely avoidable but **unusable if built**.

## Nothing was re-derived

Every supporting piece already existed, in two of the documented hiding places:

- `pow_neg_one_add_self` (`(−1)^(k+k) = 1`) and `pow_neg_one_succ`
  (`(−1)^(succ k) = −(−1)^k`) were **private helpers inside
  `int_prelude/fibonacci.rs`**, built for Cassini's identity. Exposed
  `pub(super)`, not rebuilt.
- `succ_double_eq` was likewise private in `nat_prelude/parity.rs`. Same
  treatment.
- Coprimality is **not** a hypothesis of the law: `p = succ (mul 2 m)` is odd by
  construction, and `Nat.coprime_two_left` (`Iff (gcd 2 n = 1) (Odd n)`) already
  existed. The only arithmetic it needed was `mul 2 m = add m m`, which is
  `mul_comm` plus one `zero_add` — again because `mul m 2` reduces while
  `mul 2 m` does not.

## What this does NOT claim

The **classical** `IsQuadraticResidue` form — "2 is a quadratic residue mod `p`
iff `p ≡ ±1 (mod 8)`" — is not established, and this ADR does not weaken
`int_prelude/qr_criterion.rs`'s recorded gap.

- The `≡ −1` half **does** yield a real classical statement: composed with
  `Int.euler_criterion_neg_one_imp_not_residue`, it gives *2 is NOT a quadratic
  residue mod `p` when `p ≡ 3, 5 (mod 8)`*. That composition is one application
  and is left to a caller; it is not itself declared here.
- The `≡ 1` half needs the **converse** of Euler's criterion
  (`a^((p−1)/2) ≡ 1 ⟹ a` is a residue), which needs a primitive root or a
  root-counting argument over a polynomial ring this kernel has no
  `List`/`Finset` to state. Unchanged.

`qr_criterion.rs`'s module doc says the law "is NOT reachable from these two
theorems alone" and names Gauss's lemma as the missing route. That was accurate
when written and is accurate now: the route taken is Gauss's lemma, not the
criterion.

## Evidence

- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — **278 passed, 0
  failed**.
- `cargo test -p axeyum-lean-kernel --lib int_prelude::` — **61 passed, 0
  failed**, including
  `every_int_declaration_is_checked_and_axiom_free` and
  `derived_laws_have_no_axiom_footprint`, both of which read the environment
  rather than a list.
- `second_supplementary_law_classifies_all_four_residues_mod_eight` instantiates
  at all four residue classes, **each an actual odd prime** (`m = 1, 2, 3, 8`;
  `p = 3, 5, 7, 17`; `p mod 8 = 3, 5, 7, 1`), so no numeric row is vacuous. Per
  row it checks that the class shape the law names IS `m`, that the **other
  three are NOT** (the classes genuinely separate), and that `2^m mod p` is the
  claimed sign's residue and **not** the other's. It then applies the theorem at
  a genuinely **free** `m` and compares the inferred type against an
  independently rebuilt statement, with a sign-swap control that must not be
  `def_eq`.
- Ledger: `F:int-secondsupplementarylaw`, `F:nat-half-ceil-parity`,
  `F:int-pow-neg-one-of-even`, `F:int-pow-neg-one-of-odd`.
  `validate-facts.py` — 2400 facts, 0 errors.
  `check-settled-fact-statements.py` — PASS, 2214/2214 pinned.

The classification table was re-derived in Python **before** any Rust was
written, rather than inherited from the brief:

```sh
python3 -c "
import collections
agg=collections.defaultdict(set)
for m in range(0,200):
    p=2*m+1; N=m-(m//2)
    agg[m%4].add((p%8, N%2))
for k in sorted(agg): print(k, sorted(agg[k]))
"
# 0 [(1, 0)]   1 [(3, 1)]   2 [(5, 1)]   3 [(7, 0)]
```

## Consequences

- The second supplementary law of quadratic reciprocity is established here,
  axiom-free, over constructed carriers.
- `Nat.half_ceil_parity` is reusable for anything else whose sign depends on
  `⌈m/2⌉` — the classification is stated about `sub m (div m 2)`, not about
  Gauss's lemma.
- **Retrieval note for the next lane**: `int_prelude/qr_criterion.rs`'s module
  doc is the natural place to look for this law and correctly said it was out of
  reach *from Euler's criterion*. The route is in `gauss_assembly.rs`'s
  descendants instead. The doc has not been rewritten, because its claim remains
  true as stated; the new module's own doc names the relationship.
