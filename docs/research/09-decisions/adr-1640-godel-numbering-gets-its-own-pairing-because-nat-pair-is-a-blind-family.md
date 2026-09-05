# ADR-1640: the Gödel numbering gets its own pairing, because `Nat.pair` is a blind family and its inverse needs `sqrt`

Status: accepted
Date: 2026-09-05
Lane: `arithmetization`

Index-summary: The arithmetization of `fo_syntax.rs` (`fo_code.rs`,
`fo_numbering.rs`, W3-7) does **not** reuse `Nat.pair`. Two independent
reasons: `Nat.pair`/`Nat.avg`/`Nat.unpaired` are the constants of the
**held-out** families `natural-avg-pair` and `natural-primitive-recursion`, so
proving `unpairLeft (Nat.pair a b) = a` would spend a blind evaluation
population; and `Nat.pair`'s inverse goes through `Nat.sqrt`, a fuel
recursion, so the round trip is a real arithmetic theorem on top of it.
`FO.Code.pair a b := tri (a + b) + a` is used instead — the anti-diagonal
enumeration, whose inverse is a plain `Nat.rec` iterating a **step function of
the previous pair alone**, with no division, no `sqrt` and no fuel. The round
trip costs one structural induction on the code. `FO.Term.code` and
`FO.Formula.code` are `pair tag payload` with distinct tags, and both are
proved injective. Representability of substitution, the diagonal lemma and
Gödel I did **not** land; the single obstruction is recorded, sized, below.

## Context

Roadmap item W3-7 asks for the arithmetization of the first-order syntax
ADR-1636 landed the day before: a Gödel numbering of `FO.Term` and
`FO.Formula`, injective, and then the diagonal lemma and Gödel's first
incompleteness theorem with representability of provability as an explicit
hypothesis.

Everything above the numbering rests on being able to *decode*, so the first
question is which pairing to number with, and that question turned out to have
two answers that disagree.

## Decision

### 1. A new pairing in the `FO.Code` namespace, not `Nat.pair`

`nat_prelude/avg_pair.rs` already declares `Nat.pair` (Mathlib's and Lean
core's `if a < b then b*b + a else a*a + a + b`), and `nat_prelude/unpair.rs`
declares the two projections `Nat.unpairLeft`/`Nat.unpairRight` as scalar
functions built from `Nat.sqrt`. Neither file declares a round-trip theorem,
and `unpair.rs`'s own module doc says why: "The round-trip identity
`unpairLeft (pair a b) = a` is exactly the kind of ordinary supporting theorem
that belongs in a later lane."

It does not belong in *this* lane, for a reason that doc could not know:

- **`Nat.pair` and `Nat.avg` are the constants of a held-out family.**
  `artifacts/autogenesis/nursery-v2-extension.json` carries ten
  `natural-avg-pair` rows with `"partition": "held-out"` and
  `"answer_access": "withheld-during-episode"`, whose `constants` lists name
  `Nat.pair` and `Nat.avg`; `natural-primitive-recursion` is a second held-out
  family over `Nat.pair`, `Nat.unpaired` and `Nat.Primrec`. A blind evaluation
  population is a shared resource with no owner, and touching one member
  spends the family. This lane was not given either.
- **Independently, inverting `Nat.pair` is expensive.** Its projections read
  `Nat.sqrt n` and `n - s*s`; `Nat.sqrt` is itself a fuel recursion
  (`nat_prelude/sqrt.rs`), so `unpairLeft (pair a b) = a` needs a theorem
  about `sqrt (b*b + a)` — arithmetic on top of a fuel-recursive definition,
  with a fuel-agreement lemma underneath it.

So the numbering uses its own pairing, declared under `FO.Code`, and the
existing `Nat.pair` is left exactly as it was.

### 2. The pairing is the anti-diagonal enumeration, because its inverse is structural

```text
FO.Code.tri    : Nat -> Nat                    -- 0, 1, 3, 6, 10, ...
FO.Code.pair   : Nat -> Nat -> Nat  := fun a b => tri (a + b) + a
FO.Code.step   : Nat.Pair -> Nat.Pair
FO.Code.unpair : Nat -> Nat.Pair    := Nat.rec (mk 0 0) (fun _ ih => step ih)
```

The choice is forced by what the inverse has to be. Take the other standard
injective pairing `2^a (2b+1) - 1`: its inverse is the 2-adic valuation, which
recurses on `n / 2`, which is not structurally smaller, so it needs fuel plus
a fuel-agreement lemma, and every step needs `(2m+1) % 2 = 1` and
`(2m+1) / 2 = m` — real `div`/`mod` theorems. The anti-diagonal enumeration
has a different shape: **its successor is a function of the previous pair
alone**,

```text
step (mk a 0)        = mk 0 (succ a)      -- start the next diagonal
step (mk a (succ b)) = mk (succ a) b      -- walk down this one
```

so `unpair` is `step` iterated `n` times — a plain `Nat.rec` on `n`. Both
`step` equations hold by ι-reduction, because `step` is written as a `Nat.rec`
on the pair's second component. `Nat.Pair` (`nat_prelude/binary_rec.rs`) is
the product this needs, and it already has `fst`/`snd` with computing
equations.

The round trip is then **one** structural induction, on the CODE rather than
on either component:

```text
P n := Π a b, Eq Nat (pair a b) n -> Eq Nat.Pair (unpair n) (Nat.Pair.mk a b)
FO.Code.unpair_pair a b := (Nat.rec P …) (pair a b) a b (Eq.refl _)
```

with two enumeration equations feeding it,

```text
FO.Code.pair_zero_succ : Π k,   Eq Nat (pair 0 (succ k)) (succ (pair k 0))
FO.Code.pair_succ      : Π a b, Eq Nat (pair (succ a) b) (succ (pair a (succ b)))
```

each of which is one `congrArg` over `Nat.zero_add` / `Nat.succ_add` because
everything else in it is δι. The whole slice imports exactly four `Nat`
theorems: `zero_add`, `succ_add`, `succ_injective`, `succ_ne_zero`.

### 3. Injectivity is proved through the projections, not directly

`FO.Code.fst_pair` / `snd_pair` are `congrArg` of `Nat.Pair.fst`/`snd` along
the round trip, and `FO.Code.pair_inj_left` / `pair_inj_right` follow. This
ordering matters: proving `pair a b = pair c d -> a = c` *directly* would be a
double induction with a `Nat`-level case analysis inside it, whereas via the
round trip each direction is three `Eq` steps.

That is also what makes the syntax-level injectivity affordable. Each
constructor is coded as `FO.Code.pair tag payload` with the payload nesting
field codes to the right, so

- the 12-of-16 and 72-of-81 **off-diagonal** cases are all one construction:
  `pair_inj_left` reads the two tags off the hypothesis, and distinct unary
  numerals are refuted by stripping `succ`s with `Nat.succ_injective` until
  `Nat.succ_ne_zero` applies;
- the **diagonal** cases peel the payload with
  `pair_inj_left`/`pair_inj_right`, convert each component (a `Nat` field is
  already an equality, an `FO.Term` field goes through
  `FO.Term.code_injective`, a recursive field through the induction
  hypothesis), and recombine by congruence one argument at a time.

Because the pairing is the anti-diagonal one, **small formulas get small
codes** — `⌜bot⌝ = 0`, `⌜imp bot bot⌝ = 27`, `⌜all bot⌝ = 35` — which is what
makes evaluation tests possible at all: every numeral in this kernel is unary,
and a `2^a (2b+1)` pairing would have put a two-constructor formula out of
reach of any `def_eq`.

### 4. The two numberings are separate, and that is deliberate

`FO.Term.code` and `FO.Formula.code` share `FO.Code.pair`, so a term and a
formula can have the same natural number. Injectivity is a statement *within*
each type, which is what the diagonal lemma and every representability
argument use; a single numbering across both would need one more tag level and
buys nothing here.

## Consequences

Landed, all axiom-free (`Kernel::axiom_footprint` empty, asserted after
`Environment::contains`):

```text
FO.Code.tri, FO.Code.pair, FO.Code.step, FO.Code.unpair, FO.Code.fst, FO.Code.snd
FO.Code.pair_zero_succ, FO.Code.pair_succ, FO.Code.unpair_pair
FO.Code.fst_pair, FO.Code.snd_pair, FO.Code.pair_inj_left, FO.Code.pair_inj_right
FO.Term.code, FO.Formula.code
FO.Term.code_injective, FO.Formula.code_injective
```

The decoder slice (`fo_decode.rs`) landed too, so the list above continues:

```text
FO.Term.decodeAux, FO.Term.decode, FO.Formula.decodeAux, FO.Formula.decode
FO.Code.substCode : Nat -> Nat -> Nat
FO.Code.isFormulaCode : Nat -> Bool
```

`FO.Code.unpair` is structural on the code; a **decoder is not**, because it
recurses on `FO.Code.snd n`, which is smaller than `n` but not by one
constructor. So the decoders use this prelude's standing device — a structural
recursion on a separate fuel counter with the real argument carried through
(`Nat.logAux`, `Nat.sqrtAux`, `Nat.clogAux`, `Nat.minFacAux`,
`Nat.testBitAux`, `Nat.binaryRecAux`) — and the nine-way tag dispatch is a
right-nested chain of `Nat.rec`s at a constant motive, whose LAST arm is the
catch-all.

**What is not landed is now a proof gap, not a missing construction.** The
round trip `FO.Formula.decode (FO.Formula.code p) = p` is NOT proved, so
neither is `substCode (⌜φ⌝) (⌜t⌝) = ⌜φ[t]⌝`, so the diagonal lemma still has
nothing to diagonalize and Gödel I has no sentence. Building the decoder
changed the estimate in two ways worth recording:

1. The fuel-agreement lemma is **avoidable**. State the round trip additively,
   `Π t f, decodeAux (Nat.add f (size t)) (code t) = t`, with the fuel on the
   LEFT of the `add`: `Nat.add` recurses on its right argument here, so
   `Nat.add f (Nat.succ x)` ι-reduces and the recursive call's fuel *is* the
   induction hypothesis's fuel rather than merely bounded by it. The binary
   cases then need only `Nat.add_assoc` and `Nat.add_comm` — no `Nat.le`, no
   subtraction, no `max`.
2. There is a cost nobody had counted: **one transport per tag**.
   `FO.Code.fst (code (and_ p q))` is *not* definitionally `4` —
   `FO.Code.fst` unfolds to `Nat.Pair.fst (unpair …)` and `unpair` of a
   symbolic code is stuck — so each of the 4 + 9 minors must rewrite along
   `FO.Code.fst_pair`/`snd_pair` before the tag tree ι-reduces. That was
   invisible until the tag tree existed.

`size p <= code p` remains, but only to justify the self-fuelled wrappers.
Recorded as the `open` fact `F:fo-formula-decoder`, whose statement now says
the construction is landed and the theorem is not.

Separately: ADR-1636 says the Leibniz equality rule is not in `FO.Provable`,
and the diagonal lemma's biconditional would need it. That is a *second*
prerequisite, but it is not the binding one — the decoder is.

The `F:fo-completeness-henkin` row already names "an enumeration of
`FO.Formula` and a decidable equality on it" as one of its two obstructions.
The injectivity landed here is the half of that obstruction which does not
need `Classical.em`: an injection `FO.Formula -> Nat` is what an enumeration
argument wants, and the decoder above is the other half.
