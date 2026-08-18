# ADR-0468: ℝ is constructed as a Bishop setoid over ℚ, not as a quotient or a cut

Status: accepted
Date: 2026-08-17
Index-summary: both textbook routes to ℝ cost this kernel an axiom (`Quot.sound`, or `propext`+`funext`); a setoid of regular ℚ-sequences costs **zero**, measured, and the price it pays is 9 of the 22 `Real` laws restated over a defined `Equiv` instead of `Eq`

## Context

`nat_axiom_inventory`, re-measured 2026-08-17:

```
logic: axiom=0  nat: axiom=0  integer: axiom=0  real: axiom=30  string: axiom=1
```

`Real` is now, by a wide margin, the largest item on this project's trusted
surface, and axiom-freedom is the headline metric. `integer` reached 0 since
ADR-0456 was written.

[ADR-0456](adr-0456-real-is-an-ordered-ring-modelled-by-int.md) established what
those 30 declarations are (8 carrier/operation symbols + 22 ordered-commutative-ring
laws, with no inverse, division, completeness, Archimedean or density axiom), and
exhibited ℤ as a checked model of all 22 with empty footprints. It was careful
that this is **relative consistency, not a discharge** — "`Int` is not ℝ" — and it
deferred ℝ "with a price tag", pricing exactly two routes:

- **Cauchy quotient** — needs `Quot.sound`, which this kernel's four-declaration
  quotient package does not contain.
- **Dedekind cuts** — needs `propext` and `funext`, neither of which exists.

Both prices were stated as *unavoidable*, and on that basis ℝ was not attempted.
[ADR-0457](adr-0457-reconstructions-parameterise-over-the-ordered-ring-interface.md)
then made the 30 unnecessary for *consumers* by λ-abstracting them out of Farkas
and SOS refutations, which is the right move and is already shipped — but it
eliminates the dependence on ℝ, it does not supply ℝ. Nothing in this repository
has a carrier that is actually the real numbers.

This ADR re-opens the construction question, because ADR-0456's option space was
missing an entry.

## Decision

**ℝ is constructed as a Bishop-style setoid: a carrier of *regular* Cauchy
sequences of rationals with no quotient, and equality carried by a defined
relation `CReal.Equiv` rather than by `Eq`. It costs zero trusted declarations.**

Concretely, over the ℚ that `int_prelude/rat.rs` carries and `rat_prelude.rs`
is making an ordered field:

```text
CReal.inv_succ (n : Nat) : Rat        -- 1/(n+1), via Rat.normalize
CReal.Regular (f : Nat → Rat) : Prop
  := ∀ m n, Rat.le (Rat.neg (bound m n)) (Rat.sub (f m) (f n))
          ∧ Rat.le (Rat.sub (f m) (f n)) (bound m n)
     where bound m n := Rat.add (inv_succ m) (inv_succ n)

CReal : Type                          -- one-constructor inductive, no quotient
CReal.mk : (seq : Nat → Rat) → CReal.Regular seq → CReal

CReal.Equiv (x y : CReal) : Prop      -- a DEFINITION, not Eq
  := ∀ n, |x.seq n − y.seq n| ≤ 2 · inv_succ n     -- same two-sided form
```

Note the absolute value is **not** a primitive: `|a| ≤ b` is written as the pair
`−b ≤ a ∧ a ≤ b`, so `Rat.abs` is never needed and R0 below shrinks to almost
nothing.

Four consequences are accepted deliberately, and the third is the real cost:

1. **The kernel is not changed.** No fifth quotient declaration, no `propext`,
   no `funext`, no classical axiom. The trusted surface stays where it is.
2. **`CReal` is computable.** Every operation is a definition by ordinary
   recursion on ℚ, so a concrete real reduces, in the same way `Nat.gcd` is
   executable and `Rat.reduced` is discharged by `rfl`.
3. **`Eq CReal` is not the equality of real numbers, and we never pretend it
   is.** `CReal.Equiv` is. Measured below: **9 of the 30 `Real` declarations
   mention `Eq`** (`add_comm`, `add_assoc`, `add_zero`, `add_neg`, `mul_comm`,
   `mul_assoc`, `mul_one`, `mul_zero`, `left_distrib`); the other 21 do not.
   So the setoid ℝ discharges 13 of the 22 laws verbatim and the remaining 9 in
   an `Equiv`-restated form. That is the entire price, and it is a price paid in
   *interface shape*, not in trusted declarations.
4. **The consumer interface grows an equality slot.** ADR-0457's telescope binds
   30 names and leaves `Eq` a hardwired `Const`. To instantiate it at a setoid
   carrier the telescope must also bind `eq : R → R → Prop` together with its
   equivalence and congruence laws. That is a change to
   `axeyum-solver/src/reconstruct/arithmetic/ordered_ring.rs`, sized below —
   not a kernel change.

**ℂ is scoped and deferred.** Nothing in the solver needs it (evidence below).

## Evidence

### Measurement 1 — the setoid carrier is admissible, and it is free

`crates/axeyum-lean-kernel/examples/creal_shape_probe.rs`, run against a clean
`HEAD` snapshot:

```
declaration            footprint
CReal.Of               -
CReal.Of.mk            -
CReal.Of.rec           -
CReal.Of.seq           -
CReal.Of.EquivBy       -
Control.seq_eq_self    Control.funext_seq
CReal.Of over the constructed Rat: 5 declarations admitted, trusted surface = 0 (empty)
```

The probe admits the carrier over the *constructed* `Rat` and answers the four
structural questions the plan rests on, each of which was in genuine doubt:

1. an inductive in `Type 0` may carry a **function field** `Nat → Rat`
   (`Nat → Rat : Type 0`, so no universe bump — the folklore that a real-number
   construction needs one is false here, and it is false for cuts too:
   `Rat → Prop : Type 0` as well, since `Prop : Type 0`);
2. it may carry a **dependent `Prop` field** whose type mentions the earlier
   function field;
3. the generated recursor supports **large elimination** back out to `Nat → Rat`,
   so the representative projection is a checked definition rather than an
   assumed field access; and
4. a relation over the carrier defined *through* that projection checks in
   `Prop` — the shape `Equiv` and every congruence obligation will take.

The regularity predicate and the closeness relation are **parameters** in the
probe, because both need ℚ's order (`Rat.le`, `Rat.sub`, `Rat.abs`), which does
not exist yet — `int_prelude/rat.rs` has the carrier, `normalize`, `add`, `mul`
and `neg` and no order at all. The probe says so in its own module docs and
claims only expressibility and cost. `CReal := CReal.Of Rat.Regular` is one
definition once the order lands, and nothing above changes shape.

**The zero is discriminating.** A footprint measurement that could only ever
print `-` would be worthless, so the probe carries a negative control in a second
kernel: `Control.funext_seq`, the exact monomorphic instance of `funext` a
Dedekind construction needs,

```text
∀ (f g : Nat → Rat), (∀ n, Eq.{1} Rat (f n) (g n)) → Eq.{1} (Nat → Rat) f g
```

declared as an `Axiom` and consumed by a theorem. That theorem's footprint comes
back **non-empty and naming it**. If it ever comes back empty the probe exits 1
and says the zeros above are not evidence.

### Measurement 2 — what the setoid route actually costs, counted

The type of every `Real` declaration, taken from the environment and scanned for
`Eq`:

| | count | declarations |
|---|---|---|
| mention `Eq` | **9** | `add_comm`, `add_assoc`, `add_zero`, `add_neg`, `mul_comm`, `mul_assoc`, `mul_one`, `mul_zero`, `left_distrib` |
| do not | **21** | the 8 carrier/operation symbols and the 13 order/inequality laws |

```sh
cargo run -q -p axeyum-lean-kernel --example nat_axiom_inventory 2>/dev/null \
  | awk -F'\t' '$1=="real"{print $4}' \
  | while read -r h; do printf '%s' "$h" | xxd -r -p \
      | grep -q 'Eq\.' && echo EQ || echo NOEQ; done | sort | uniq -c
#   9 EQ
#  21 NOEQ
```

So the setoid ℝ satisfies 13 of the 22 laws *as written* and 9 of them only
after `Eq` is replaced by `Equiv`. The often-repeated claim that a setoid
"infects every downstream theorem" overstates it by a factor of two here: the
order fragment — which is what a Farkas refutation actually invokes — is
untouched.

### Measurement 3 — the two rejected routes are still closed

Re-verified rather than quoted from ADR-0456:

- `QuotKind` has exactly four variants (`Type`, `Ctor`, `Lift`, `Ind`) in
  `env.rs`, `quotient.rs` has `PACKAGE_LEN = 4`, and the string `sound` does not
  occur in `quotient.rs`. No `Quot.sound`.
- `propext`, `funext`, `Classical` and `choice` do not occur as declarations
  anywhere in `crates/axeyum-lean-kernel/src/`. The only textual hits are a
  doc comment in `lean_pp.rs` describing what real Lean's `#print axioms`
  reports, and an unrelated word in `tc.rs`.

### Measurement 4 — nothing in this solver needs ℂ

Swept across code, docs, ADRs and the fact ledger. The IR's `Sort` enum has no
complex sort; no SMT-LIB logic in scope involves ℂ; and every decision procedure
is real- or rational-valued. Real algebraic numbers (ADR-0038, ADR-0046) are
*real-root isolation*: grepping `nra_real_root.rs`, `sturm.rs`, `poly.rs` and
`real_algebraic.rs` for `complex|imaginary|algebraically closed` returns exactly
**one** hit across all four, and it is `#[allow(clippy::type_complexity)]` —
i.e. zero substantive occurrences. (Stated as the raw count rather than as
"zero", because a claim written as a grep result has to survive re-running the
grep, and this one did not the first time.) The Nullstellensatz route in
`cas_poly.rs:591` is explicit that it never needs algebraic closure — "The
system then has no common zero over any field containing ℚ, so none over ℝ and
none over ℤ." There is no CAD.

Two *shipped* consumers of a small piece of ℂ exist, and neither is analytic:

- `axeyum-cas/src/geometry_certify.rs` has `struct Gaussian { real, imaginary }`
  — exact ℚ(i) — because a cofactor identity holds in every ℚ-algebra, so its
  **negative controls must be able to live in ℂ** (`x² + y²` has isotropic
  directions `(1, ±i)` that have no real counterexample). ~80 lines, already
  written, needs only ring arithmetic and a zero test.
- `axeyum-cas` reserves the symbol `I` with `I² = −1` folded into the zero test —
  a quotient of a polynomial ring, not a number type.

The planned ℂ work (CAS phase C4b / G17) is gated behind factorization and
unscheduled, and `docs/curriculum/curriculum.toml` marks the `complex` node
terminal (`unlocks = []`, `status = "lean-horizon"`).

## Prior art

The relevant question is not "Cauchy or Dedekind" but **"where does equality come
from"**, and the systems split on it rather than on the representation.

| system | ℝ obtained by | equality | trusted cost |
|---|---|---|---|
| **Coq/Rocq stdlib** (`Reals.Raxioms`) | **axiomatized** | primitive | ~17 axioms incl. `completeness` and the *informative* `total_order_T`, which is classical |
| **Coquelicot** | a *layer over* the axiomatic ℝ | inherited | inherits all of the above |
| **CoRN** (C-CoRN, Nijmegen) | constructive, **setoid** (`CSetoid`, book equality `[=]` with apartness `#`) | a defined relation | none beyond the base logic |
| **Lean 4 / Mathlib** | `CauSeq.Completion.Cauchy` over ℚ — a **quotient** | `Eq`, via `Quot.sound` | `propext`, `Quot.sound`, `Classical.choice` |
| **Isabelle/HOL** | Cauchy sequences via `quotient_type` over ℚ | `Eq` (HOL) | none — `typedef` is a conservative definitional extension, but HOL is classical and extensional *by construction* |
| **HOL Light** | Harrison's "nearly-additive" sequences on ℕ | `Eq` | none beyond HOL's axioms |
| **Metamath** `set.m` | Dedekind-style cuts of positive rationals | set equality | none beyond ZFC |

Two things in that table are load-bearing for us.

**First, the systems that pay nothing for ℝ are the ones that already paid.**
Isabelle/HOL and HOL Light get `Eq`-based quotients "for free" only because HOL's
logic is classical and has extensionality as a *primitive rule*; Metamath gets
cuts for free because ZFC has extensionality as an *axiom*. Our logic prelude has
neither, at zero trusted declarations, which is precisely why `Int.eq_em` had to
be a restricted decidable equality rather than excluded middle. We are in the
constructive type theory column, and the only system in that column that
constructs ℝ with no additional trusted surface is **CoRN, by setoid**. That is
the precedent this ADR follows.

**Second, Lean's own numbers do not support the "quotient is standard" reading.**
Mathlib's `Real` is a quotient (`CauSeq.Completion.Cauchy` over ℚ) and its
footprint carries `Quot.sound`, `propext` *and* `Classical.choice`; a `Real` fact
in Mathlib is a three-axiom fact. But Lean **core**'s `Rat` is a normalised
structure with proof fields and no quotient at all
(`Init/Data/Rat/Basic.lean:33`, same pinned toolchain) — which is exactly the move
`int_prelude/rat.rs` already copied, deliberately, and the move `Int` made with
`ofNat`/`negSucc`. Following Lean's *quotient* for ℝ while having followed Lean's
*structure* for ℚ and ℤ would be picking the worse half of Lean's design.

Third, the folk trade-off between the two representations does not survive
contact with this kernel:

- **Dedekind does not avoid a quotient's axiom — it substitutes a worse one.** A
  cut is a predicate `Rat → Prop`, and proving two cuts with the same members
  `Eq` needs `funext` *and* `propext`. In Lean, `funext` is itself *derived from*
  `Quot.sound` — read out of the toolchain this repository already pins rather
  than recalled, `Init/Core.lean:2281` in `leanprover--lean4---v4.30.0`:

  ```lean
  theorem funext {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}
      (h : ∀ x, f x = g x) : f = g := by
    let eqv (f g : (x : α) → β x) := ∀ x, f x = g x
    let extfunApp (f : Quot eqv) (x : α) : β x := Quot.liftOn f …
    exact congrArg extfunApp (Quot.sound h)
  ```

  So a Dedekind ℝ in a Lean-shaped kernel does not escape the quotient
  primitive; it needs it *plus* `propext`. Two trusted items where the quotient
  route needs one, which is what ADR-0456 recorded — and the reason "cuts avoid
  the quotient" is exactly backwards here.
- **Neither representation needs a universe bump here**, contrary to the usual
  telling. Measured above: `Nat → Rat : Type 0` and `Rat → Prop : Type 0`.
- **The choice therefore falls to computation, and Cauchy wins.** A regular
  sequence *is* an algorithm producing a rational approximation at any requested
  precision; a cut computes nothing. This kernel prizes definitional reduction
  (`Nat.gcd` executable, `Rat.reduced` by `rfl`) and the eventual consumers are
  interval arithmetic and algebraic-number refinement, which need to evaluate.
- **Bishop's *regular* sequences, not bare Cauchy sequences.** Fixing the modulus
  to `|f m − f n| ≤ 1/(m+1) + 1/(n+1)` removes the existential quantifier from
  the carrier, so the representative type stays a plain function, the modulus
  never has to be extracted, and — the reason it matters later — completeness
  becomes provable **without countable choice**. Bare Cauchy sequences make
  Cauchy-completeness of ℝ a choice principle; that is the trap the HoTT book's
  chapter 11 goes to a higher inductive type to escape, and a fixed modulus
  escapes it more cheaply.

## Alternatives

**Add `Quot.sound` and build the Cauchy quotient (Mathlib's route).** Rejected.
It buys a genuine `Eq` — the 9 `Eq`-laws would be discharged as written and the
consumer interface would not change — at the cost of extending a validated,
byte-contracted four-declaration trusted package to five. `nat_axiom_inventory`
would then read `real: axiom=0 quotient=5`, and every real fact's footprint would
read `[Quot.sound]` forever. The inventory counts `Quotient` as trusted
deliberately, so this is not an accounting trick that gets us to zero; it moves
the 30 into 1 and makes it permanent and un-eliminable. Reconsider only if the
`Equiv`-restated laws prove intolerable downstream, which Measurement 2 says is
unlikely for the order fragment that Farkas actually uses.

**Dedekind cuts.** Rejected: `funext` + `propext`, two trusted items instead of
one, plus a carrier that computes nothing. Note this is a *strictly worse* trade
than the quotient, not a cheaper one — which inverts the usual intuition and is
worth recording, because "cuts avoid the quotient" is the reason a lane would
reach for them.

**Redefine `Real := Rat`.** Rejected for the same reason ADR-0456 rejected
`Real := Int`: every gate stays green while every reconstructed theorem silently
weakens. Worth stating again because ℚ *does* satisfy all 22 laws and *is*
adequate for LRA — rational and real satisfiability coincide for linear systems
with rational coefficients — so the temptation here is real. ℚ is the right
carrier for LRA; it is not ℝ, and the difference shows up the moment an
Archimedean, supremum, or `√2` statement appears.

**Do nothing; rest on ADR-0457.** Rejected as the plan, accepted as the *current
state*. Generalizing consumers over the interface makes the 30 unnecessary, which
is why `real: axiom=30` is not urgent. But an interface with no model that is
actually ℝ cannot state a theorem *about* the real numbers, and the north star is
a complete framework for reasoning, not a complete framework for reasoning about
whatever satisfies 22 hypotheses.

## Implementation plan

Sized in declarations, not lines, because the kernel's cost is per-declaration.
For calibration: `int_prelude` is 7,898 lines for 54 derived theorems, and
`nat_prelude` carries 165 named declarations.

**Phase R0 — ℚ as an ordered field (prerequisite, owned by `agent-rationals`,
essentially met).** Re-measured while writing this ADR, and the answer changed
mid-draft: `crates/axeyum-lean-kernel/src/rat_prelude.rs` (in the worktree, not
yet committed at the time of writing) already declares `Rat.zero`, `one`, `le`,
`lt`, `inv`, `sub`, `div`, the cross-multiplication bridge
(`eq_of_cross`/`cross_of_eq`/`normalize_congr`) and **all 22 ordered-ring laws**
over the `Rat` carrier that `int_prelude/rat.rs` declares. An earlier draft of
this ADR said "ℚ has no order at all", which was true of `int_prelude/rat.rs`
and false of the development that supersedes it — the standing trap that a tool
pointed at the wrong subject returns a confident wrong answer.

What R1 additionally needs is therefore small and is **not** `Rat.abs` (see
above): `CReal.inv_succ n := Rat.normalize (Int.ofNat 1) (Nat.succ n) h`, with
`h : 1 ≤ n+1` immediate from the `Nat` order development. One definition and one
lemma. Anything else this lane discovers missing is a request to
`agent-rationals`, not a fork of ℚ.

**Phase R1 — the carrier (~12 declarations).** `CReal.inv_succ`, `CReal.Regular`,
`CReal`, `CReal.mk`, `CReal.rec` (generated), `CReal.seq`, `CReal.regular` (the
two projections), `CReal.Equiv`, and `Equiv`'s three equivalence laws (`refl`,
`symm`, `trans`). Shape already measured admissible by `creal_shape_probe`.

`trans` is the one proof in R1 that is not routine, and the shape of it is worth
recording so nobody loses a session to the obvious dead end. Chaining the two
hypotheses directly gives `|x_n − z_n| ≤ 4/n`, which is **not** `≤ 2/n`, and no
amount of rearranging fixes that. Bishop's argument compares at an *arbitrary*
third index `j`:

```text
|x_n − z_n| ≤ |x_n − x_j| + |x_j − y_j| + |y_j − z_j| + |z_j − z_n|
            ≤ (1/n + 1/j) + 2/j + 2/j + (1/j + 1/n)  =  2/n + 6/j
```

and then discharges the `6/j` with a lemma **about ℚ, not about ℝ**:

```text
Rat.le_of_le_add_inv_succ : (∀ j, a ≤ b + 6 · inv_succ j) → a ≤ b
```

which is the Archimedean property of ℚ and is provable from the `Nat`/`Int`
developments. It is the only genuinely new ℚ lemma the whole construction needs,
it belongs in `rat_prelude` rather than here, and it should be requested from
`agent-rationals` at the start of R1 rather than discovered in the middle of it.
This is also precisely the step a bare-Cauchy development does not have — it is
the price of the fixed modulus, paid once.

**Phase R2 — the ordered ring (~35 declarations).** `CReal.zero`, `one`, `add`,
`neg`, `mul`, `le`, `lt`, each with its regularity proof (that is the work —
`add` and `neg` are immediate, `mul` needs a canonical bound derived from
regularity, and the bound is where a naive port from Mathlib will not
transfer because Mathlib gets it from `CauSeq`'s existential modulus). Then the
22 laws: 13 verbatim, 9 as `Equiv`. Then the **congruence** obligations that are
the setoid's actual tax — `add`, `mul`, `neg` respect `Equiv`, and `le`/`lt` are
`Equiv`-invariant. Five more, and they are unavoidable.

**Phase R3 — the interface's equality slot (~1 module in `axeyum-solver`).**
`generalize_over_ordered_ring` gains a telescope variant binding
`eq : R → R → Prop` plus `eq_refl`/`eq_symm`/`eq_trans` and the five congruences,
with the 9 `Eq`-laws' types rewritten through it. `RING_BINDER_NAMES` goes 30 →
39. Instantiating at `Eq` recovers today's `FullInterface` exactly, which is the
test: the existing five fixtures must reproduce their current statements. This
is the only work outside the kernel crate, and it is the one that makes a
constructed ℝ *usable* rather than merely present.

**Phase R4 — the instantiation (~1 declaration + 1 example).** `CReal` supplied
to the R3 telescope, with an `arith_model`-shaped witness module
(`Real.CRealModel.<law>`) computing each interpreted type from the environment
rather than writing it by hand, and a `creal_model_witness` example whose exit
status depends on all 22 witnesses having empty footprints. At that point
`build_int_model_of_arith`'s relative-consistency result is superseded by an
actual model of ℝ, and ADR-0456's "`Int` is not ℝ" caveat is discharged.

**Realistic end state, stated honestly.** `real: axiom=0` is reachable, and by
*deletion* rather than by proof: once R3 lands, no consumer references the
`Real` package, and `build_arith_prelude` can be retired. The constructed
`CReal` adds **zero** trusted declarations — measured, not projected. What is
*not* on offer is `Eq CReal` as real-number equality; it is `CReal.Equiv`, and
every downstream statement about reals will say so. Anyone who wants `Eq` pays
`Quot.sound` and should re-run this ADR's accounting first.

**Explicitly out of scope, with triggers.** Completeness (`exists_isLUB`),
Archimedean-ness, `Rat.inv`-based division on `CReal`, and `√`. None is needed
by the 22 laws, and each is a separate ADR. Archimedean and division are cheap
over regular sequences; completeness is where the choice-principle question
returns, and the fixed modulus is what will make it answerable without one.

**ℂ: deferred, priced.** Over a constructed `CReal`, ℂ is a two-field structure
with pointwise `add`/`neg`, the usual `mul`, and no order — roughly 15
declarations, all mechanical, and no new trusted item. But Measurement 4 found no
consumer: the only shipped complex arithmetic in this repository is exact **ℚ(i)**
in `geometry_certify.rs`, which needs a ring, not a field, and not ℝ underneath.
So the correct near-term move is **ℚ(i) over the constructed ℚ** — a Gaussian-integer-style
pair structure with `Eq` (ℚ(i) has canonical representatives, so no setoid is
needed and it is strictly cheaper than ℂ) — and ℂ proper waits for CAS phase C4b
or a Lean-facing analysis goal. Do not build ℂ to have built ℂ.

## Consequences

- **The option space in ADR-0456 was incomplete, and the correction is
  actionable.** Its two rejections were both correct; the conclusion "therefore
  ℝ is deferred" did not follow, because equality does not have to be `Eq`.
  ADR-0456 is not superseded — its measurements stand and its model of the
  package in ℤ stands — but its Alternatives section should be read alongside
  this one.
- **`creal_shape_probe` is a standing ratchet on the four structural facts.** If
  a kernel change breaks large elimination out of a `Type`-valued inductive with
  a `Prop` field, or makes a function field inadmissible, the probe fails before
  a lane has invested in Phase R2.
- **The prerequisite is met sooner than expected, and the ADR was wrong about
  it for one draft.** `rat_prelude.rs` landed ℚ as an ordered field while this
  was being written, so R1 is unblocked as soon as that lane commits; the only
  gap is `1/(n+1)`, and stating `|a| ≤ b` as `−b ≤ a ∧ a ≤ b` removes the
  `Rat.abs` dependency entirely. Recorded rather than quietly fixed, because the
  wrong version was read off a file (`int_prelude/rat.rs`) that was genuinely
  authoritative a day earlier.
- **ADR-0457's telescope is now known to be one binder short of extensible.**
  Hardwiring `Eq` was invisible while every candidate carrier had decidable
  canonical representatives (ℤ, ℚ). The first carrier that does not is ℝ, and
  it is the last one, so R3 is a one-time cost.
- Revisit when: `Quot.sound` is proposed for the quotient package (redo the
  accounting — a genuine `Eq` may then be worth one permanent footprint entry),
  when a `Real` axiom mentioning a supremum or Archimedean-ness is proposed
  (Phase R1–R2 become prerequisites rather than options), or when the CAS
  factorization phase C2 lands and G17 makes ℂ a real consumer rather than a
  curriculum node.
