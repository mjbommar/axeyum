# ADR-1669: the order symbol was already in the signature, so Q-with-order is six axioms and not a new ℕ structure

Status: accepted
Date: 2026-09-06
Lane: `fo-diagonal-lemma`
Roadmap: W3-7, fourth slice (follows ADR-1636, ADR-1640, ADR-1648, ADR-1651)

Index-summary: ADR-1651 left the uniqueness half of representability blocked —
Q has no induction and none of its seven axioms constrains a variable, so
`Q ⊢ ∀z (z + z = m̄ → z = k̄)` is not derivable. The textbook repair is the order
axioms. Two things about how they land here were decided by measurement rather
than preference. **`≤` cannot be a second symbol**: `FO.natStructureQ`'s binary
relation family is `rel2 k x y := Nat.lt (Nat.add x k) y`, so `rel2 0` is `<`
and `rel2 1` is `x + 1 < y` — no index of that family is `Nat.le`, and adding
one would mean a second ℕ structure and a re-proof of `FO.Q.natModels` at it. So
`x ≤ y` is spelled `x < S y`, six axioms are added, and `FO.Qle` conses them in
FRONT of `FO.Q` so the tail after the sixth cons is definitionally `FO.Q` and
`FO.Qle.natModels` is six `And.intro`s over `FO.Q.natModels v`. **The binder
order `∀y∀x` is forced**: `all_elim` on `all (all φ)` puts the outer instance
under `FO.Subst.lift`, i.e. under `FO.Term.subst t FO.Subst.shift`, which
ι-reduces for a `var` or a closed literal term and is repairable by
`FO.Term.subst_numeral` for a stuck symbolic numeral, but is **unrepairable for
a `Π (t : FO.Term)`-bound term** — nothing is known about it. Numeral outer and
arbitrary term inner is therefore the only order in which this family can be
instantiated at `(numeral n, arbitrary term)`, which is what the bounded case
split of the next slice needs. Nine declarations, all axiom-free; three mutants
run, one of which refuted its own prediction and thereby established that the
axiom-shape test is not subsumed by admission.

Index-status: accepted

## Context

`fo_robinson.rs` (ADR-1651) landed Robinson's Q as an `FO.Context`, its ℕ model,
its consistency, numeral arithmetic, and the **positive** half of
representability for the pairing (`FO.Q.pair_represented`). It stopped at the
uniqueness half and said why: *from Q4–Q7 one can compute with numerals and
nothing else*, so no statement of the form `∀z (… z …)` with `z` genuinely
constrained is derivable. `fo_robinson/tests.rs` asserts the ABSENCE of any
`FO.Q.pair_unique` rather than leaving that gap as prose.

The standard repair in the literature is Q⁺ — Q with the order constrained —
plus a numeral case split, and then Σ₁-completeness on top. This slice lands the
theory, its model and its consistency. It does **not** land the case split, the
negative numeral twin, uniqueness, or the diagonal lemma; the sized obstructions
for those are in the closing section.

## Decision

### 1. Six order axioms over the existing `<`, not a new symbol and not a schema

| | axiom | reading |
| --- | --- | --- |
| O1 | `∀x, ¬(x < 0)` | nothing is below zero |
| O2 | `∀y∀x, x < S y → (x < y ∨ x = y)` | discreteness, downward |
| O3 | `∀y∀x, x < y → x < S y` | discreteness, upward (left) |
| O4 | `∀x, x < S x` | discreteness, upward (right) |
| O5 | `∀y∀x, x < S (x + y)` | `x ≤ x + y`, the `∃`-characterisation ⇐ |
| O6 | `∀y∀x, x < S y → ∃z (x + z = y)` | `x ≤ y → ∃z (x+z=y)`, ⇒ |

O2 with O3 and O4 is the discreteness biconditional `x < S y ↔ (x < y ∨ x = y)`;
O5 with O6 is the standard order axiom `x ≤ y ↔ ∃z (x + z = y)`. Each is written
as separate implications because `FO.Formula` has no `iff` constructor, and
adding one was judged more expensive than stating both halves — a judgement this
slice can now support with a number rather than an estimate, since each half
cost one `Definition` and one one-line ℕ obligation.

**There is one formula per row, not one per numeral.** `FO.Qle` is a
finitely axiomatised theory with no induction axiom and no induction schema, so
it stays strictly weaker than PA and Gödel I remains applicable to it. The
bounded case split the next slice needs is proved by induction *outside* the
calculus, one derivation per numeral.

### 2. `≤` is not a second symbol — a measured obstruction, not a preference

`FO.natStructureQ`'s binary relation family is

```text
rel2 := fun k x y => Nat.lt (Nat.add x k) y
```

so `rel2 0` ι-reduces to `Nat.lt` (because `Nat.add x 0` ι-reduces to `x`; this
kernel's `Nat.add` recurses on its right argument) and `rel2 1` to
`Nat.lt (Nat.succ x) y`, i.e. `x + 1 < y`. The index adds to the LEFT argument,
and `Nat.le x y` is `Nat.lt x (Nat.succ y)` — an increment on the RIGHT. **No
index of that family is `Nat.le`**, so `≤` could only be a second symbol at the
cost of a second ℕ structure, and then `FO.Q.natModels` would have to be
re-proved at it. `fo_order/tests.rs` pins this with `def_eq` at concrete small
arguments: `rel2 0 2 5` is `Nat.lt 2 5`, and `rel2 1 2 5` is neither that nor
`Nat.le 2 5`.

Spelling `x ≤ y` as `x < S y` costs nothing: it is what `≤` means in ℕ, and O2
and O4 are what make it mean that inside the theory.

### 3. The order axioms go in FRONT of `FO.Q`

`FO.Qle` is the six consed onto `FO.Q`'s seven, so the context tail after the
sixth cons is definitionally `FO.Q`. `FO.Qle.natModels` is then six
`And.intro`s over `FO.Q.natModels v` rather than a re-proof of the seven
Robinson obligations. `fo_order/tests.rs` pins the tail identity directly, with
a coverage control that the tail after FIVE conses is NOT `FO.Q` — so the row
pins the count as well as the contents.

### 4. The binder order is `∀y∀x`, and it is forced

In every binary row the OUTER quantifier is the *bound* `y` and the inner one is
the *subject* `x`. Instantiating `all (all φ)` at `(t₁, t₂)` via
`FO.Provable.all_elim` puts `t₁` under `FO.Subst.lift`, i.e. under
`FO.Term.subst t₁ FO.Subst.shift`. That application:

- **ι-reduces** when `t₁` is a `FO.Term.var i` (`subst (var i) shift` reduces to
  `var (i+1)`) or a closed literal term;
- is **stuck but repairable** when `t₁` is `FO.Term.numeral a` at a symbolic `a`
  — a `Nat.rec` stuck on `a`, and `FO.Term.subst_numeral` (`fo_robinson.rs`) is
  the lemma that unsticks it;
- is **stuck and unrepairable** when `t₁` is a `Π (t : FO.Term)`-bound term,
  because nothing is known about it and no lemma can be stated.

The next slice's bounded case split has the shape
`Π (n : Nat) (t : FO.Term), Provable Qle (imp (lt t (numeral (S n))) (upto n t))`
and applies O2 at `(numeral n, t)`. With the binders the other way round the
arbitrary `t` would land in the outer position and the derivation would be
impossible — not merely awkward. Writing the axioms in the wrong order would
have been discovered one slice later, after they were fixed.

## Consequences

Nine declarations, all axiom-free, all pinned by
`cargo run --release -p axeyum-lean-kernel --example fo_order_inventory --
--require-axiom-free --expect-count 9`:

```text
FO.Qle                  definition  FO.Context
FO.Qle.axLtZero         definition  FO.Formula
FO.Qle.axLtSuccCases    definition  FO.Formula
FO.Qle.axLtSuccStep     definition  FO.Formula
FO.Qle.axLtSelfSucc     definition  FO.Formula
FO.Qle.axLtAddRight     definition  FO.Formula
FO.Qle.axLtDest         definition  FO.Formula
FO.Qle.natModels        theorem     Π v, FO.ctxSat AxNat FO.natStructureQ FO.Qle v
FO.Qle.consistency      theorem     Not (FO.Provable FO.Qle FO.Formula.bot)
```

`F:fo-qle-order-context` and `F:fo-qle-consistency` record the two theorems.

### The mutation that refuted its own prediction

Three mutants were run against `fo_order::tests`, in release.

1. `axLtZero` from `x < 0` to `x ≤ 0` (i.e. `x < S 0`) — false in ℕ at `x = 0`.
   Predicted: the model theorem fails to admit. **Ran: 9 of 9 tests killed**,
   `KernelError::TypeMismatch` raised by `Kernel::add_declaration` at prelude
   build. Prediction held.
2. `axLtAddRight` from `x < S (x + y)` to `x < S (y + x)`. Chosen *because it
   stays TRUE in ℕ*, predicting that the model theorem would still admit and
   only the axiom-shape test would die. **Ran: 9 of 9 killed**, again at prelude
   build. **The prediction was wrong**, and the reason is worth recording:
   `FO.Qle.natModels` does not check that an axiom is true in ℕ, it checks that
   the *supplied witness inhabits the goal* — and `Nat.add y x` is not
   definitionally `Nat.add x y` in this kernel, since commutativity is a theorem
   and not a reduction. So any change to an axiom's syntactic form invalidates
   its witness, whether or not the axiom stays true.
3. The same mutation with the witness repaired consistently — `Nat.le_add_right`
   transported along `Nat.add_comm`. Predicted: the prelude admits again and
   exactly one test dies. **Ran: exactly one died**
   (`the_order_axioms_are_the_stated_formulas`), 8 passed.

Mutant 3 is what mutant 2 was meant to be, and it is the one that carries the
finding: **a self-consistent wrong axiom-plus-witness pair is caught by the
`def_eq` shape test and by nothing else in this module.** Without it the honest
report would have been "I have no evidence the shape test has teeth beyond
admission", because mutants 1 and 2 are both killed by the trusted gate and say
nothing about the test. This is the "self-consistent errors defeat per-step
checks" hazard in `CLAUDE.md`, met head-on rather than assumed away.

## What did NOT land, and the sized obstruction for each

The brief's deliverables 2–4 are not attempted here; the coordinator narrowed
scope to deliverable 1 mid-session. The sizing below is from reading the
derivations through, not from attempting them, and is stated so the next lane
can start from it rather than re-deriving it.

**The negative numeral twin** `a ≠ b → Qle ⊢ ¬(ā = b̄)`. ADR-1651 sized this as
"generalise five helpers (`Rob::prov_q`, `q_axiom_derivation`, `all_elim_at`,
`cast_derivation`, `leibniz`) over the context". **That sizing is pessimistic
and this ADR withdraws it.** `FO.Provable.weaken : Π g p q, Provable g p →
Provable (cons q g) p` lifts any `Qle` derivation into `cons φ Qle` in one step,
so the helpers can stay at the fixed context and only the steps that genuinely
*use* the hypothesis — `ax_head`, `eqf_subst`, `imp_elim`, all of which already
take their context explicitly — need a context argument. The remaining work is
three object-level derivations plus a double `Nat.rec`:

- `0̄ ≠ (S a)‾` needs symmetry of `eqf`, which is one `eqf_subst` at the shape
  `eqf (var 0) 0̄` (no numeral repair: `0̄` is `FO.Term.f0 0`, a closed literal);
- `(S a)‾ ≠ 0̄` is essentially free — `axSuccNeZero` instantiated at `numeral a`
  is already `imp (eqf (S ā) 0̄) bot`, with no stuck numeral, because the numeral
  enters only through the substituted variable and not literally in the body;
- the successor step needs `axSuccInj` at `(ā, b̄)`, i.e. the two-deep numeral
  repair `fo_robinson.rs`'s private `instantiate_binary_axiom` already performs;
- the double `Nat.rec` on `(a, b)` needs the contrapositive of `Nat.succ`
  injectivity, which is `gcongr` plus function composition.

Estimate: one file of roughly 400–500 lines, no new kernel machinery.

**The bounded case split** `Qle ⊢ ∀z (z < S n̄ → z = 0̄ ∨ … ∨ z = n̄)`. Needs a
new `Definition` `FO.Qle.upto : Nat → FO.Term → FO.Formula` by `Nat.rec`, then a
`Nat.rec` on `n` whose base is O1 + `bot_elim` and whose step is O2 followed by
`or_elim`/`or_intro`. The term-schematic form (`Π (t : FO.Term)`) is the one to
state, and it is available only because of decision 4 above. **One unmeasured
risk**, flagged rather than assumed: the object-level `∀z` form needs
`all_intro`, whose premise context is `FO.Context.shift FO.Qle`. That should
ι-reduce back to `FO.Qle` because every axiom is a closed formula, but it
requires δ-unfolding all thirteen axiom constants and traversing each — and **no
existing derivation in this group uses `all_intro` over a non-empty context**
(`FO.provable_all_imp_self` uses it at `nil`, where `Context.shift nil` reduces
in one step). Whether that reduction happens, and what it costs, should be
measured with a throwaway derivation BEFORE any lane commits to the ∀ form.

**Uniqueness of representation for `pair`.** With the twin and the case split in
hand the route is: O5 at `(z, z)` gives `z < S (z + z)`; `eqf_subst` against the
hypothesis `z + z = m̄` turns that into `z < S m̄`; the case split gives
`z = 0̄ ∨ … ∨ z = m̄`; each disjunct `z = j̄` with `j ≠ pair(a,b)` is refuted by
`add_numeral` plus the negative twin. The obstruction is that `m = 2·pair(a,b)`
is **symbolic**, so the disjunction has symbolically many disjuncts and its
elimination is itself a `Nat.rec` producing a derivation from a uniform family
`Π j, j ≤ n → Provable (cons (eqf t j̄) Γ) φ`. That eliminator is the piece of
machinery none of the four slices so far has needed.

**The diagonal lemma.** Blocked on representability of `diag`, which is blocked
on uniqueness. Gödel I stays open and hypothesis-carrying, as ADR-1651 left it.

## Alternatives rejected

**A second ℕ structure with `≤` interpreted at `rel2 1`.** Rejected on the cost
in decision 2: `FO.Q.natModels` would have to be re-proved at it, and every
`FO.Q` theorem would then live over a context whose structure differs from the
one the arithmetization uses. The `x < S y` spelling is free.

**An `iff` constructor on `FO.Formula`.** Rejected: it would need a clause in
`FO.sat`, a case in `fo_soundness.rs`'s induction, a code in `fo_code.rs`, and a
case in every `fo_roundtrip.rs` injectivity proof — five files touched to save
three `Definition`s here.

**Stating the order axioms as a schema over numerals** (`x ≤ n̄ → x = 0̄ ∨ … ∨
x = n̄`, one axiom per `n`). Rejected: it would make `FO.Qle` an infinite
context, which `FO.Context` cannot express as a value, and it would move work
that belongs in the metatheory into the theory. The schema-free O1/O2 pair
proves every instance by induction outside the calculus, which is where the
induction belongs if the theory is to stay weaker than PA.

## Links

- [adr-1636-first-order-model-theory-lands-de-bruijn-and-the-eigenvariable-condition-is-a-shift.md](adr-1636-first-order-model-theory-lands-de-bruijn-and-the-eigenvariable-condition-is-a-shift.md)
- [adr-1640-godel-numbering-gets-its-own-pairing-because-nat-pair-is-a-blind-family.md](adr-1640-godel-numbering-gets-its-own-pairing-because-nat-pair-is-a-blind-family.md)
- [adr-1648-the-round-trip-carries-its-fuel-and-leibniz-needed-no-induction.md](adr-1648-the-round-trip-carries-its-fuel-and-leibniz-needed-no-induction.md)
- [adr-1651-robinson-q-is-a-context-and-the-two-fo-chains-must-share-one-syntax.md](adr-1651-robinson-q-is-a-context-and-the-two-fo-chains-must-share-one-syntax.md)
