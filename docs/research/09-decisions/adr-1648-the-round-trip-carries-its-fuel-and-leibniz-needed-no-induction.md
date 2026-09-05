# ADR-1648: the decoder round trip carries its fuel explicitly, and the Leibniz rule needed no induction

Status: accepted
Date: 2026-09-05
Lane: `fo-diagonal`

Index-summary: The decoder round trip `decodeAux (Nat.add f (size t)) (code t)
= t` is proved for `FO.Term` and `FO.Formula`, with the fuel on the **left** of
the `Nat.add` — load-bearing, because `Nat.add` recurses on its right argument
here, so `Nat.add f (Nat.succ x)` ι-reduces and the recursive call's fuel IS
the induction hypothesis's. Everything downstream is stated at **explicit
fuel**, because the self-fuelled `decode n := decodeAux n n` would need
`Nat.le (size p) (code p)` and that is **false** (`FO.Formula.code
FO.Formula.bot` is `Nat.zero`, its size is `1`) — measured, not conjectured.
So `FO.Code.substCodeAux_commutes` (the commuting lemma),
`FO.Code.isFormulaCodeAux_code` and `FO.Code.diagAux_code` (the arithmetization
half of the diagonal lemma, `diag ⌜p⌝ = ⌜p(⌜p⌝)⌝`) all take fuel arguments.
The **Leibniz rule** `eqf_subst` lands as `FO.Provable`'s seventeenth
constructor with its soundness case, and ADR-1636's estimate that it needed a
fifth induction over `FO.Formula` was wrong: `FO.sat_inst` already reduces
`sat (φ[t]) w` to `sat φ (Val.cons M (eval t w) w)`, where the term appears
only as a **value**, so the case is one `Eq.rec`. The provability-level
diagonal lemma did **not** land; its obstruction is representability in Q and
is sized below.

## Context

ADR-1640 landed the Gödel numbering, its injectivity and the decoder
*construction*, and recorded three predictions about what the round trip would
cost. ADR-1636 landed `FO.Provable` with `eqf_refl` as its only equality rule
and recorded the Leibniz rule as the next increment, with an estimate of its
cost. This lane discharged all four claims. Three were right, one was wrong,
and the one that was wrong was wrong in our favour.

## Decision

### 1. The round trip is stated additively, with the fuel on the LEFT

```text
FO.Term.decode_code    : Π t f, Eq FO.Term
     (FO.Term.decodeAux (Nat.add f (FO.Term.size t)) (FO.Term.code t)) t
FO.Formula.decode_code : Π p f, Eq FO.Formula
     (FO.Formula.decodeAux (Nat.add f (FO.Formula.size p))
                           (FO.Formula.code p)) p
```

with `FO.Term.decode_code_at_size` / `FO.Formula.decode_code_at_size` as the
`Nat.zero_add` corollaries.

ADR-1640's prediction (a) was exactly right, and the mutation confirms it is
load-bearing rather than stylistic: flipping the statement to
`Nat.add (size t) f` makes the kernel reject `FO.Term.decode_code` with
`TypeMismatch`, killing all twelve of the module's tests. `Nat.add` recurses on
its right argument in this prelude, so `Nat.add F (Nat.succ x)` ι-reduces to
`Nat.succ (Nat.add F x)` and the decoder's step body appears at fuel
`Nat.add F (size child)` — *literally* the induction hypothesis's fuel, not
merely a bound on it. With the fuel on the right nothing reduces.

`size` is a **sum**, not a `max`: `size (f2 k a b) = succ (add (size a) (size
b))`. A `max` would drag `Nat.le` and its case analysis into every one of the
thirteen minors; the sum costs one `Nat.add_assoc` for the right child and an
`Nat.add_comm` under `Nat.add F ·` before the same `Nat.add_assoc` for the
left one, and nothing else. ADR-1640's prediction that only `add_assoc` and
`add_comm` would be needed was right.

ADR-1640's prediction (b) — one transport per tag — was also right and is what
the thirteen minors are made of. `FO.Code.fst (FO.Code.pair 4 x)` is not
definitionally `4`, because `FO.Code.fst` unfolds to `Nat.Pair.fst (unpair …)`
and `unpair` of a symbolic code is a stuck `Nat.rec`. Each minor therefore
opens with a transport along `FO.Code.fst_pair`, after which the scrutinee is a
literal numeral and the nine-way tag tree ι-reduces to its arm; the arm's
payload projections are then rewritten one at a time along
`FO.Code.fst_pair`/`FO.Code.snd_pair`, and finally each non-`Nat` field is
closed by the induction hypothesis (or, for a `FO.Term` field of a
`FO.Formula` constructor, by `FO.Term.decode_code`).

### 2. Everything downstream takes fuel arguments, because `size ≤ code` is FALSE

ADR-1640's prediction (c) was that the self-fuelled wrapper
`FO.Formula.decode n := decodeAux n n` needed `Nat.le (size p) (code p)`. The
first half is right; the second is not merely unproved but **refutable**:

| `x` | `size x` | `code x` |
| --- | --- | --- |
| `FO.Term.var 0` | `1` | `FO.Code.pair 0 0` = `Nat.zero` |
| `FO.Formula.bot` | `1` | `FO.Code.pair 0 0` = `Nat.zero` |

Both rows are pinned by `Kernel::def_eq` in
`fo_roundtrip/tests.rs::size_is_not_bounded_by_the_code`, so this is a
measurement and the fact ledger can carry it.

So this lane does **not** state any theorem about `FO.Code.substCode` or
`FO.Code.isFormulaCode`. It declares fuel-explicit siblings and states the
theorems there:

```text
FO.Code.substCodeAux : Nat -> Nat -> Nat -> Nat -> Nat
FO.Code.substCodeAux_commutes : Π p t gp gt, Eq Nat
     (substCodeAux (Nat.add gp (FO.Formula.size p))
                   (Nat.add gt (FO.Term.size t))
                   (FO.Formula.code p) (FO.Term.code t))
     (FO.Formula.code (FO.Formula.subst p (FO.Subst.cons t FO.Subst.id)))

FO.Code.isFormulaCodeAux : Nat -> Nat -> Bool
FO.Code.isFormulaCodeAux_code : Π p g, Eq Bool
     (isFormulaCodeAux (Nat.add g (FO.Formula.size p)) (FO.Formula.code p))
     Bool.true
```

**The alternative was considered and rejected.** One could keep the
self-fuelled wrappers and prove them by strong induction on the code, using
`Nat.lt (FO.Code.snd n) n` — true, because `FO.Code.pair a b` is strictly
larger than `b`. That needs monotonicity of `FO.Code.tri`, a `Nat.lt`
development on top of it, and a well-founded recursion. It is a slice, not a
step, and it buys only the removal of two `Nat` arguments from four statements.

The two fuel arguments of `substCodeAux` are separate rather than one shared
fuel, deliberately: with one, the commuting lemma would need an
`add_assoc`/`add_comm` shuffle to hand the same number to two different
`size`s. With two it needs none, and the statement is the one a caller wants
anyway.

### 3. The Leibniz rule is `FO.Provable`'s seventeenth constructor, appended

```text
eqf_subst : Π g p s t, Provable g (eqf s t)
              -> Provable g (Formula.subst p (Subst.cons s Subst.id))
              -> Provable g (Formula.subst p (Subst.cons t Subst.id))
```

Appended at index 16 so no existing rule index moves, and `FO.soundness` gains
a seventeenth minor rather than being restructured. `FO.soundness` and
`FO.consistency` stay green and axiom-free.

**ADR-1636's estimate was wrong, and measurably.** It recorded that the
soundness case would need "a congruence of `FO.sat` along an equality between
the evaluations of two terms under a substitution, which is a fifth induction
over `FO.Formula`". It is not. `fo_substitution.rs`'s `FO.sat_inst` already
says

```text
Iff (sat (Formula.subst p (Subst.cons t Subst.id)) w)
    (sat p (Val.cons M (Term.eval M S t w) w))
```

and on the right the term `t` occurs **only** as the value `Term.eval M S t w`
— a `Nat`-indexed valuation entry, not a subterm of `p`. So the minor is
`sat_inst` forward at `s`, one `Eq.rec` at the motive
`fun x => sat p (Val.cons M x w)` transporting that value along the hypothesis,
and `sat_inst` backward at `t`. No induction at all.

The rule is stated with the substitution on **both** sides for exactly this
reason. A form in which `s` occurred literally inside `φ` would have needed the
induction ADR-1636 predicted; this form does not, and the difference is the
whole content of the decision.

The general lesson, which is why this is in an ADR and not only a comment: a
cost estimate for a soundness case is a claim about **where the syntax appears
in the semantics**, and `FO.sat`'s substitution lemma had already moved it from
"inside a formula" to "as a value". Re-read the lemmas you already have before
believing a predecessor's sizing.

### 4. The diagonal lemma lands as its arithmetization half only

```text
FO.Term.numeral   : Nat -> FO.Term
FO.Code.diagAux   : Nat -> Nat -> Nat -> Nat
FO.Code.diagAux_code : Π p gp gt, Eq Nat
     (diagAux … (FO.Formula.code p))
     (FO.Formula.code (FO.Formula.subst p
        (FO.Subst.cons (FO.Term.numeral (FO.Formula.code p)) FO.Subst.id)))
```

`diagAux_code` is `diag ⌜p⌝ = ⌜p(⌜p⌝)⌝`, one application of
`substCodeAux_commutes`. `FO.Term.numeral` uses symbols `f0 0` and `f1 1` so
the numeral denotes its own index in `FO.natStructure`, whose interpretation is
`fn0 k = k` and `fn1 k x = Nat.add x k`.

**The provability-level statement did not land**, and the obstruction is a
strand rather than a step. `FO.Provable Γ_Q (Iff δ (ψ ⌜δ⌝))` requires `Γ_Q` to
*prove* the numeric fact `diag m̄ = ⌜δ⌝` — that is, the diagonal function must
be **representable in Q**, which for a `Nat.rec`-defined function is
Σ₁-completeness. Three separate things are missing, and none is proof-term
engineering:

1. Nothing in `fo_*.rs` relates `FO.Provable` to a computation on `Nat` in
   either direction. There is no theorem of the form "if `Nat.beq a b` is
   `Bool.true` then `Provable Γ_Q (eqf ā b̄)`", which is the base case of
   Σ₁-completeness and needs `Γ_Q` written down as an explicit `FO.Context` of
   Q's seven axioms plus an induction over the numerals.
2. `FO.Formula` has no `Iff` connective; the statement is
   `and_ (imp a b) (imp b a)`, which is fine but means the lemma's shape has to
   be chosen rather than inherited.
3. Representability of `diag` itself requires representing `FO.Code.pair`,
   `FO.Code.tri`, `FO.Code.unpair` and the fuel recursion — i.e. a
   Σ₁-definition of each, which is where the bulk of the work is.

`FO.Term.numeral` and `diagAux` are what a later lane needs in order to start
(1); they are landed so that lane does not have to choose the numeral encoding
again.

### 5. A measured hazard: the diagonal is not EVALUABLE at any genuine code

Every `Nat` numeral in this kernel is unary, and `diagAux (code p)` contains
`FO.Term.code (FO.Term.numeral (FO.Formula.code p))`. At the smallest formula
with a free variable — `FO.Formula.eqf (var 0) (var 0)`, code `2` — the numeral
is a three-constructor term with code `47`, and the diagonalised formula's code
is `FO.Code.pair 1 (FO.Code.pair 47 47)`, over ten million. At
`FO.Formula.rel1 0 (var 0)` (code `5`) the first draft of the test **overflowed
the stack**, measured on this host.

So `FO.Code.diagAux` is pinned by `Kernel::def_eq` at three FREE variables —
pure δ/β, no numerals — plus a negative control that its fourth argument is the
code of the *numeral* of `n` and not `n` itself. Any later lane writing an
evaluation test against the diagonal should expect the same wall, and should
not read the absence of a concrete evaluation test as an oversight.

## Consequences

- `crates/axeyum-lean-kernel/src/fo_roundtrip.rs` is the new slice, registered
  from the crate root; `examples/fo_code_inventory.rs` now builds
  `build_fo_roundtrip_prelude` so the `F:fo-code-*` evidence covers it.
- `fo_provable.rs` and `fo_soundness.rs` changed additively only: one appended
  constructor, one appended minor, `rules: [NameId; 16]` → `[NameId; 17]`.
  Every existing rule index is unchanged.
- The arithmetization package is 61 declarations over `build_nat_prelude`
  (48 before this lane), pinned with a coverage control so drift in either
  direction fails.
- `F:fo-formula-decoder` stays `open`: what it states is the SELF-fuelled
  round trip, which section 2 shows is not reachable from `size`. The
  fuel-explicit theorems are new rows.
- `F:fo-diagonal-lemma` stays `open`, but one of its two recorded
  prerequisites — "no Leibniz rule" — is now discharged, and the other is
  refined from "needs a decoder" to "needs representability in Q".

## Mutation evidence

| mutant | prediction | run |
| --- | --- | --- |
| round trip's fuel on the RIGHT (`Nat.add (size v) f` in `round_trip_at`) | kernel rejects `decode_code`; the ι-reduction argument is load-bearing | RUN — `TypeMismatch`, 12 of 12 tests failed |
| commuting lemma with `code t` and `code p` swapped in `substCodeAux`'s arguments | kernel rejects `substCodeAux_commutes` | RUN — `DeclarationValueMismatch`, 12 of 12 tests failed |

Both mutants were applied in this lane's own worktree, run to completion, and
the file restored byte-for-byte (`git status --porcelain` empty afterwards).
