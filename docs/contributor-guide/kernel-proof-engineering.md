# Kernel Proof Engineering — getting a declaration admitted

Why `Kernel::add_declaration` rejected your term, and which of these failures it
cannot detect at all. Every entry is a measured incident, kept because the
failure mode recurs; the trigger index lives in
[CLAUDE.md](../../CLAUDE.md#gotchas), which points here.

Read this before building a new `Definition` or a proof term over an unfamiliar
carrier. The companion documents are
[Prelude Build Cost](prelude-build-cost.md) (the same kernel, but slow rather
than wrong) and [Finding Existing Lemmas](finding-existing-lemmas.md) (the step
that comes first).

## The one-line summary

The kernel type-checks; it does not know what you meant. A `Definition` has no
proof body, so a function that computes the WRONG VALUE still has the right
type and is admitted. Every guard this repository leans on — `axiom_footprint`,
the `every_*_declaration_is_checked_and_axiom_free` tests, the prelude build —
is blind to it. Only evaluation at concrete arguments can see it.

## A concrete instantiation can hide the bug a symbolic one exposes

**A CONCRETE INSTANTIATION CAN HIDE THE BUG A SYMBOLIC ONE EXPOSES, so the
mandatory-instantiation rule is NECESSARY AND NOT SUFFICIENT.** Measured
2026-08-26 in `creal/exponential.rs`. A proof of `2^n <= 2*n!` type-checked at
every concrete `n` tried (2, then 3) and failed with `TypeMismatch` for
symbolic `n`. The cause was real: `Int.int_le_of_mul_le_mul_right`'s
conclusion is `a * (ofNat c)`, ONE multiplication, while the chain produced
`(a * d1z) * d2z`, two left-associated ones -- propositionally equal, not
definitionally. At a concrete `n` every term reduces to a numeral and full
evaluation papers the associativity hole over.

This cuts against the instinct the rest of this file builds. Concrete
instantiation is what catches a transposed branch, a sign error, and a wrong
hand-computed expectation -- three separate defects this session, none of
which a symbolic check would have found. But numerals reduce, and reduction
hides every defeq-shaped gap. The two checks fail on disjoint defect classes,
so a declaration needs BOTH: instantiate at concrete arguments AND confirm the
proof term builds against a genuinely free variable.

The bisect that finds it: run `Kernel::infer` on each intermediate step with a
FREE fvar in the position, not a literal, and compare the inferred shape
against what the next lemma's conclusion expects. The first step whose shape
differs is the one needing an explicit `mul_assoc` (or `add_assoc`) rewrite.

**AND THE ERRORS CAN BE MUTUALLY CONSISTENT, WHICH DEFEATS CHECKING THE
INTERMEDIATES ONE BY ONE.** Measured 2026-08-29 on `Int.fib_two_mul`. Five
`isymm(a, b, h)` call sites had their arguments backwards relative to the
hypothesis actually in hand — and **each individually type-checked**, because
each was checked against an expectation that was backwards in the same way.
A concrete `n = 3` test passed every named intermediate cleanly. The defect
surfaced only when the pieces were chained through `itrans` at a genuinely
free `n`.

So "instantiate concretely AND check symbolically" is right, and *where* you
check symbolically matters: a per-step symbolic check can pass on a chain that
does not compose. The technique that found it was to re-derive the whole proof
against a real `fresh_fvar` pushed into an explicit `LocalContext`, checking
each named intermediate with `infer_in`/`def_eq_in` — the free variable is
what makes a self-consistent pair of reversals disagree.


## `le_congr`'s premise takes the pre-substitution type

**`le_congr`'s PREMISE TAKES THE PRE-SUBSTITUTION TYPE, AND AN `Equiv` PROOF IN
A `le` SLOT FAILS IDENTICALLY TO A DIRECTION BUG.** Measured across 2026-08-26.
Eleven separate rejections in one session came from this family, in six
different files, and every one presented as an opaque `TypeMismatch`:

- `le_congr(x, x', y, y', hxx', hyy', h)` needs `h : le x y` — the type
  **before** the rewrite. A lane twice passed a proof about a sub-term where
  the whole product's bound was needed; the kernel rendered `Equiv A A` (the
  reflexivity witness for the wrong side) against `A`'s unfolded definition.
- The same call needs `Equiv x' x`, not `Equiv x x'`, when `h` is about `x`.
  Getting `x`/`x'` backwards is the single most common bug in this
  development.
- **`Equiv` and `le` are different props.** Passing `equiv_refl` into an
  `add_le_add` slot that wants `le_refl` produces a failure indistinguishable
  from either of the above.

Three habits that actually work, each of which produced a first-attempt
kernel accept the same day:
- **Mirror an existing helper's construction** rather than building a term by
  hand. Two lanes reported first-attempt accepts from this alone.
- **Check a lemma's stated direction rather than assuming it matches its
  neighbour.** `Rat.sub_add_add`'s direction is the OPPOSITE of
  `sub_add_sub`'s, in the same file.
- When both sides of a `TypeMismatch` are multi-hundred-KB and `Read` cannot
  load them, **write a small differ**. One lane found a swapped `rsymm` that
  way in minutes.


## `Nat.add` and `Nat.mul` recurse on their RIGHT argument

**`Nat.add` RECURSES ON ITS RIGHT ARGUMENT, so `Nat.add(literal, k)` IS STUCK
FOR SYMBOLIC `k` — and it fails by not reducing, not by erroring.** Measured
2026-08-25 while normalizing a `CReal` bound: two fusion steps built
`Nat.add(8, k)` instead of `Nat.add(k, 8)`, and the term never reduced to
`succ^8(k)`. The kernel reported a `TypeMismatch` deep inside an unrelated
`Rat.le` cross-multiplication unfold, several rewrites away from the cause.

What makes it worth its own entry is the SECOND-order damage: the whole
construction had been designed so that every `K`-containing accumulator stays
the left operand, which keeps the index arithmetic **pure defeq and needs no
`Nat.add_assoc`/`Nat.add_comm` at all**. Putting the literal on the left does
not merely produce a stuck term — it silently forfeits that property, so the
proof would need associativity and commutativity lemmas everywhere it
previously needed none.

The rule: **when a `Nat.add` will be padded, compared, or fused, the symbolic
side goes LEFT and the literal RIGHT.** If a term mysteriously will not reduce
and the error surfaces far from the arithmetic, check the operand order before
anything else.

**`Nat.mul` HAS THE SAME ASYMMETRY, AND IT DECIDES WHICH EQUATION IS `refl`.**
Measured 2026-08-29. `Nat.mul` also recurses on its RIGHT argument, so
`mul_succ : mul n (succ m) = add (mul n m) n` is refl-provable, while the
left-successor form `succ_mul : mul (succ n) m = add (mul n m) m` is a real
induction-proved THEOREM. A lane building `mul_lt_mul_right` copied the
left-hand core's `mul_succ` shortcut and assumed `mul (succ b) a` reduced the
same way. It does not: the assumption poisoned **all 169** `nat_prelude::`
tests with one `TypeMismatch`. Fixed with an explicit transport along
`succ_mul`.

So the rule generalises: **before assuming an arithmetic equation holds by
`Eq.refl`, check which argument the operation recurses on.** The mirrored form
is a theorem, not a reduction, and copying a sibling proof's shortcut across
the mirror is how you find out.

**AND IT DECIDES WHICH VARIABLE A CASE TREE MUST SPLIT ON.** Measured
2026-08-29 building the `Nat.bit` decode bridge. `bit test k` puts
`cond test 1 0` in `Nat.add`'s SECOND position, so — because `add` eats the
right argument — **`bit true k` is `succ`-shaped for ANY `k`, even a symbolic
one, while `bit false k` needs `k`'s own shape exposed.** The first draft
split its case tree on the `Nat` operands and the kernel rejected it with an
opaque `TypeMismatch`; splitting on the **Bool** is what works.

The technique that found it, and it is the one to reach for whenever both
sides of a `TypeMismatch` are too large to read: a throwaway probe test that
renders both mismatched sides with `Kernel::render_lean` and diffs them.


## A recursor applied to a bare free variable is stuck

**A RECURSOR APPLIED TO A BARE FREE VARIABLE IS STUCK — AND FOR A
TWO-ARGUMENT DEFINITION YOU MUST KNOW *WHICH* ARGUMENT IT RECURSES ON.**
The `Nat.add` entry above is one instance of a general rule: a free variable
is not a constructor, so any `Nat.rec` on it simply does not reduce.

Measured 2026-08-28 on `Nat.choose`, which is a **two-argument** structural
recursion — outer `Nat.rec` on the FIRST argument, inner on the second
(`nat_prelude/choose.rs`, the `outer_motive` / `row` construction). So
`choose(succ a, k)` reduces and `choose(a, k)` does not, for any `k`
whatsoever. A lane's `choose_le_succ` base case assumed `choose(a, 0)` was
defeq to `1` for symbolic `a`; it is not, and the fix was to route through
the equation lemma `choose_zero_right(a)` rather than rely on reduction.

The rule: **before assuming a defeq, check which argument the definition
recurses on, and confirm that argument is constructor-shaped in your goal.**
An equation lemma exists for exactly this case — reach for it rather than
hoping the term reduces.


## When is flipping an `ml430` mirror honest?

**WHEN IS FLIPPING AN `ml430` MIRROR HONEST? THE TEST IS WHETHER MATHLIB
*DEFINES* IT THAT WAY OR *PROVES* IT ABOUT A DIFFERENT DEFINITION.**

Ten definition lanes have created new `F:nat-*`/`F:int-*` facts rather than
flipping the `ml430` mirror, on the standing rule that "our construction is
not Mathlib's". That rule is right far more often than not, but it was being
applied as a blanket, and a blanket rule cannot tell you when a flip WOULD be
honest. The criterion, checkable per fact at the Mathlib source:

> **If Mathlib's `def` is the same function, the mirror is our statement and
> flipping it is honest. If our definitional BODY is Mathlib's THEOREM about
> a structurally different `def`, the mirror is a different proposition and
> must stay open.**

Both outcomes occurred in one session, which is why the distinction is worth
having:

- **`Nat.descFactorial_of_lt` — flip.** The landed lemma already stated
  `F:ml430-nat-descfactorial-of-lt`'s `formal.statement` verbatim. A quarter
  of that lane's task was evidence plus a status flip, no proof work.
- **`Nat.multichoose` — must stay open.** A lane fetched
  `Mathlib/Data/Nat/Choose/Basic.lean` at the pinned commit `c5ea0035…`
  rather than inferring from prose. Mathlib's is a **three-case double
  recursion** (`multichoose n (k+1) + multichoose (n+1) k`), and
  `multichoose_eq : multichoose n k = (n + k - 1).choose k` is a **proved
  theorem** about it. Ours *defines* that formula as the body. So we define
  what Mathlib proves, about a different function. All three mirrors stayed
  open and the lane wrote no code.

**Compare the fact's `formal.statement` against the landed lemma's RENDERED
TYPE** (`nat_theorem_inventory`), never against a doc comment or a module
banner — and when it matters, read Mathlib's actual source at the pinned
commit. Prose has been wrong about this repository's own contents repeatedly.

Note the residue: showing our formula and Mathlib's recursion agree at every
argument needs an induction relating **two independently-built `Nat.rec`
instances**. The `bitwise` lane hit the same wall from the other side
(`bitwise and m n = land m n` is true at every concrete `{0,1}` pair and not
definitionally equal at symbolic operands). That is a real, recurring
boundary, not a gap in either lane's effort.


## The trusted gate cannot tell you a `Definition` is wrong

**THE TRUSTED GATE CANNOT TELL YOU A `Definition` IS WRONG. ONLY EVALUATION
CAN.** `Kernel::add_declaration` type-checks a proof term against its stated
type. A `Definition` has no proof body — it is admitted once it is
well-typed, and a function that computes the WRONG VALUE still has the right
type. `Nat → Nat → Nat` is `Nat → Nat → Nat` whatever it returns.

So for a definition, "the kernel accepted it" means *well-formed*, not
*correct*. Every guard this repository leans on — `axiom_footprint`,
`every_*_declaration_is_checked_and_axiom_free`, the prelude build — is blind
to a definition that means something other than what you intended.

Three instances in one day, each caught by a lane *reasoning*, not by the
kernel:

- **`Nat.lor`.** `Nat.land`'s `fuel = m` shortcut is sound only because AND
  has an **absorbing zero** (`m = 0` ⇒ result 0 regardless of `n`). OR has no
  absorbing element, so the same base case would **silently drop every bit of
  `n` whenever `m = 0`** — `lor 0 1000000 = 0`. Type-correct, admitted, wrong.
  Fixed by returning `n` at fuel exhaustion, which is sound because `m` is
  fully halved to 0 well within `m` steps.
- **Bézout witnesses.** `↑(gcd x y) = x·gcdA + y·gcdB` is satisfied by *some*
  pair for **any** correct gcd, so type-checking the identity pins down
  nothing about what `gcdA` returns. The lane added evaluation at 13 points
  across all four sign branches, and it caught its own wrong hand-computation
  at `(1,1)`.
- **`Nat.descFactorial`.** Concrete instantiation is where `Nat.sub`'s silent
  truncation actually bites, and only evaluation past the base exercises it.

**So: every new `Definition` needs an evaluation test** — reduce it to normal
form at concrete arguments and compare against independently computed values.
Two rules that make the test worth having:

- **Pick arguments that DISCRIMINATE.** `land 3 5 = 1` and `lor 3 5 = 7` use
  the same numeral pair deliberately, so a copy-paste between the two files
  fails loudly instead of passing.
- **Keep the magnitudes small** — unary numerals mean `whnf` walks towers
  (one declaration: 2,426 unfolds against **291,261 attempts**, 98% of them
  `Nat.succ`). `land 3 5` is right; `land 512 1875` would cost more than the
  whole prelude.

**The specific rule the bitwise family yielded, since it decides
correctness rather than style.** A fuel-recursive binary definition here has
the shape `Aux m m n` — the `m` operand supplies **both** the fuel and the
value halved toward structural zero. So the fuel-exhaustion base case is
determined by ONE question:

> **Does the FUEL operand carry this operator's absorbing zero?**

| definition | fuel operand absorbing? | base case | why |
| --- | --- | --- | --- |
| `Nat.land` | yes (`0 AND n = 0`) | constant `0` | safe |
| `Nat.lor` | **no** (`0 OR n = n`) | return **`n`** | constant `0` would give `lor 0 1000000 = 0` |
| `Nat.ldiff` | yes (`ldiff 0 n = 0`) | constant `0` | same reason as `land`, **not by analogy** |
| `Nat.bit` | — non-recursive | no device at all | |

`ldiff` is the instructive one: it takes `land`'s base case but its inner
succ-row guard is a **hybrid** — the `n = 0` branch returns `m` (`lor`'s
shape, since `ldiff m 0 = m`), the `m = 0` branch returns `0` (`land`'s).
**One-sided absorption gives a mixed definition**, and copying either
template wholesale produces a wrong one that type-checks.

**AND THE GENERAL FORM DOES NOT HAVE TO RECONCILE THOSE FOUR BASE CASES — IT
DERIVES THEM.** I briefed a lane that "any agreement proof must line up the
base cases first, and they are not the same shape across the four." That was
wrong, and the lane refuted it while landing
`Nat.bitwise_and_eq_land` / `Nat.bitwise_or_eq_lor`.

`bitwiseAux`'s general fuel row is `if f false true then n else 0`. For a
**concrete** `f`, that reproduces each sibling's hand-chosen row **by δβι
alone**: `and false true = false → 0`, matching `land`'s constant `0`;
`or false true = true → n`, matching `lor`'s `n`. Same for the succ row via
`f true false`. **Every base case is `refl`, no lemma.** The absorbing-zero
rule decided what each *sibling's* row had to be; `bitwise` re-derives the
same answer from `f` itself.

The real difficulty is the **per-bit combine** —
`bool_select_nat (f (beq (m%2) 1) (beq (n%2) 1)) 1 0` against `mul (m%2) (n%2)`
— both stuck at symbolic operands and equal only once each bit is known to be
`0` or `1`. Four leaves under a doubled `cases_mod_two`, each `refl`.

**`Nat.mod_two_eq_zero_or_one` had to be built**, and the search for it is
instructive: the *ingredients* existed inline in `powsq.rs`'s
`declare_even_or_odd` (a `Bool.rec` on `beq r 0`, plus a private
`mod_two_eq_one_of_ne_zero` giving only the `= 1` half), immediately consumed
into a `div`-shaped conclusion that never mentions `Nat.mod`. Hiding place 2
exactly. `binary.rs`'s seven `mod _ 2` sites use `Lt r 2` as a bound and never
split it. Grep proof BODIES, not names.

**FUEL-IRRELEVANCE NEEDS A *DOUBLE*-FUEL INDUCTION, BECAUSE THE SINGLE-FUEL
ONE IS SELF-REFERENTIAL.** `Nat.land_aux_eq_land_of_le :
∀ fuel m n, Le m fuel → Eq (landAux fuel m n) (land m n)` landed, and the
obvious route does not work: `land m n` unfolds to `landAux m m n`, putting
the same value back in the fuel slot, so an induction on one fuel needs the
canonical instance to unfold and refers to itself. The fix is to generalize
over **two independently-chosen sufficient fuels**
(`agree_by_double_fuel_induction`, `ops.rs`); the single-fuel statement is
then a one-line corollary at `fuel2 := m` via `le_refl`, since defeq handles
`land m n ≡ landAux m m n`.

The hypothesis must be `Le m fuel`, **not** unconditional: `landAux 0 m n = 0`
for any `m > 0` while `land m n` need not be. Callers always arrive with
MORE than canonical fuel (`land_bit` unfolds at `fuel = bit a m`), never
less. Pin the negative control at insufficient fuel — `(1, 7, 7)` gives
`landAux 1 7 7 = 1` against `land 7 7 = 7` — or the statement could be
quietly false and the kernel would prove it anyway.

**A NEGATIVE CONTROL COPIED FROM A SIBLING OPERATOR CAN BE VACUOUS, AND I
KEPT TELLING LANES TO COPY ONE.** `land`'s insufficient-fuel witness
`(fuel, m, n) = (1, 7, 7)` — where `landAux 1 7 7 = 1` against
`land 7 7 = 7` — **does not discriminate `lor` at all**: both sides give 7,
so the "control" passes while checking nothing. The transporting lane found
this, and picked `(1, 3, 4)` for `lor` (`lorAux = 5` vs `lor = 7`) and
`(0, 7, 0)` for `ldiff` (`0` vs `7`) instead — **simulating each recursion in
Python first**, before committing to a Rust proof.

So: **derive the witness from the operator you are testing, and check it
actually separates the two sides before you build anything around it.** A
control inherited from a neighbouring proof is exactly the shape that looks
rigorous and measures nothing — the failure this file warns about everywhere
else, arriving through the door marked "reuse".

**Two more corrections from that transport, both about `lor`:**

- The sizing "~20 lines each" held **exactly** for `ldiffAux` (its
  `zero_left_any_fuel` is byte-for-byte `land`'s) and **not** for `lorAux`,
  which needed a nested `cases_zero_succ` on `n`: `bool_select_nat_same` does
  not apply because `lor`'s two guard branches are `m` and the reduced `n` —
  *different terms*, not one repeated.
- **What broke `lor` was its fuel-exhaustion ROW (returns `n`, not `0`), not
  its guard order.** The absorbing-zero rule predicts the row correctly; what
  it does not predict is that the row's shape then propagates into the
  *proof* of every lemma above it.

**AND IT PROPAGATES INTO THE *STATEMENT*, NOT ONLY THE PROOF — THE
UNCONDITIONAL FORM CAN BE FALSE.** Measured 2026-08-29 transporting
`land_comm`'s same-fuel commutativity to `lorAux`.
`Nat.land_aux_comm_of_fuel : ∀ fuel m n, landAux fuel m n = landAux fuel n m`
needs **no hypotheses at all**, because `landAux`'s fuel-exhaustion row is the
absorbing constant `0` and is therefore symmetric for free. The obvious `lor`
analogue is not merely harder to prove — it is **false**:

    lorAux 0 0 1 = 1     against     lorAux 0 1 0 = 0

because the pass-through row returns `n`, which is not symmetric in `m`/`n`.
So `Nat.lor_aux_comm_of_fuel` must carry `Le m fuel → Le n fuel`, and both
places need them: the base case (the hypotheses force `m = n = 0`, restoring
symmetry) and the both-nonzero step (bounding each half for the IH).

**FOR A SYMBOLIC COMBINATOR THE BOUNDARY ROWS NEED IT TOO, WHICH IS NOT
OBVIOUS.** Measured 2026-08-29 proving `Nat.bitwise_comm` over a symbolic
`f`. The unconditional form is false whenever `f false true = true` (so for
`or` and `xor`, and true only for `and`) — confirmed by Python simulation
before any Rust — so the proof takes `lor`'s shape plus an explicit
`hf : ∀ a b, f a b = f b a` that neither `land` nor `lor` ever needed. `hf`
is required in **two** places: the per-bit combine, which is expected, and
the `m = 0` / `n = 0` **boundary**, which is not — for symbolic `f` the two
boundary rows are *different partial applications of `f`*, where for a
concrete operator they reduce to comparable constants.

**AND WHEN TRANSPORTING A *PROOF*, CHECK THE NESTING ORDER OF ITS CASE
SPLITS — COPY-PASTING A CLOSING WRAPPER SILENTLY CLOSES OVER THE WRONG
BINDERS.** Measured 2026-08-29 executing `lor_assoc` from `land_assoc`'s
shape. `land`'s hard leaf nests its two dichotomies **Y-outer / X-inner**;
`lor`'s nests them the **opposite** way. The copied closing wrapper therefore
captured the outer `X`-dichotomy's binders where it needed its own inner
`Y`-dichotomy's. Caught by self-review before the first compile — but it
would have surfaced as an opaque `TypeMismatch` naming neither dichotomy.

So a transported proof needs its **binder structure** re-derived, not only
its lemma names re-pointed. The tell is a wrapper referring to fvars whose
names match the source proof rather than the one you are writing.

The rule to carry: **when transporting a lemma between these operators, ask
first whether the fuel-exhaustion row is symmetric in the two operands.** If
it is not, the transported statement needs sufficiency hypotheses that the
original did not, and writing the unconditional version wastes the attempt on
a false goal. Simulate both recursions in Python at small arguments before
writing any Rust — that is what caught this one, and it is the same step that
catches a vacuous negative control.

**And fuel-irrelevance is NECESSARY BUT NOT SUFFICIENT for the 7 facts a
triage attributed to it.** `land_comm`/`land_assoc`/`land_bit` and their
`lor`/`ldiff` siblings each need something further — a `Nat.bit` decode
bridge, or a same-fuel commutativity lemma. The triage's "these 7 reduce to
fuel-irrelevance" was the right diagnosis of a *blocker* and an optimistic
reading of a *cost*; I relayed it as the latter. Transport to `lorAux`/
`ldiffAux` is ~20 lines each (the induction machinery and arithmetic helper
carry over; only a per-auxiliary any-fuel base case is new).

**Fuel-irrelevance is a SEPARATE piece and is not needed for agreement.**
`bitwise f m n := bitwiseAux f m m n` and `land m n := landAux m m n` put the
*same expression* in the fuel slot, so one counter decrements in lockstep and
there are never two fuels to reconcile. But **7 open `natural-bitwise` facts
(`land_comm`, `land_assoc`, `lor_comm`, `lor_assoc`, `land_bit`, `lor_bit`,
`ldiff_bit`) DO need it** — unfolding `landAux` at `fuel = bit a m` arrives at
a non-canonical fuel. `agree_by_fuel_induction`'s `statement` closure returns
an arbitrary `Prop`, so `fun fuel => ∀ m n, Le m fuel → …` is directly
expressible in it.

Per-bit combination is a separate choice with its own reasoning: `land` uses
the `Nat` **product** of two values in `{0,1}`, `lor` uses `max` via
`ble` + `bool_select_nat` (a product is wrong for OR), `ldiff` uses
`beq` + `bool_select_nat`. Pick it from the operator's truth table, not from
the neighbouring file.

**Asymmetric operators hand you the best negative control for free**:
`ldiff 3 5 = 2` against `ldiff 5 3 = 4`, with an explicit assertion that the
swapped value does NOT `def_eq`. `land`/`lor` are commutative and cannot
offer that, which is why they use a shared numeral pair across files instead.

A theorem *about* the definition is not a substitute. It constrains the
definition only as far as the theorem's own content reaches, which for an
existence statement is often not at all.


## "Needs a factorization product" is not "needs multiset uniqueness"

**"NEEDS A FACTORIZATION PRODUCT" IS NOT "NEEDS MULTISET UNIQUENESS", AND
CONFLATING THEM DECLARES A WHOLE AREA UNREACHABLE THAT IS NOT.** Measured
2026-08-30, correcting a sizing I had propagated into a brief.

`nat_prelude/factorization.rs` proves factorizations EXIST and its module doc
correctly says uniqueness is not attempted and **cannot be** — this kernel has
no `List`/`Finset`/product type in which to state multiset equality. That is
true and it stays true. What does not follow is the conclusion drawn from it:
that the three remaining totient mirrors were blocked.

The distinction: the classical **Euler-product route** evaluates a closed form
`φ(n) = n·∏(1−1/p)`, and evaluating a product over "the" prime factors does
need them to be canonical. But each of those targets is instead **PRESERVED
ALONG A CHAIN of prime steps** — the chain is built from *some* factorization
of the cofactor, and nothing in the argument ever compares two factorizations.
Uniqueness is only needed to evaluate; it is not needed to induct.

The whole input set turned out to be `exists_prime_dvd` (far weaker than
unique factorization), `euclid_lemma`, `gcd_mul_right`, and the prime step
`φ(q^(j+1)) = q^(j+1) − q^j` — which needs no factorization at all, being a
direct `countRange` argument. Six theorems landed, every one admitted on the
first attempt.

**The general test, when a documented impossibility seems to block a target:
ask whether the argument EVALUATES the unavailable object or merely INDUCTS
past it.** An existence lemma plus an induction reaches a great deal that a
closed form cannot.

One control worth copying from that lane, because it nearly wrote the opposite:
a composite control on `φ(x) ∣ φ(x·q)` is **vacuous** — that statement holds
at composite `q` too, so it fails at zero of them, and the composite control
that genuinely discriminates the prime-power *formula* would have produced a
check that cannot fail. Its suite now MEASURES that (0 failures) and uses
transposed divisibility instead (142 failures). When reusing a control across
two statements in one family, re-derive that it still separates.


## A goal constraining only a bounded projection needs no deep induction

**IF THE GOAL ONLY CONSTRAINS A BOUNDED PROJECTION OF A RECURSIVE VALUE, YOU
DO NOT HAVE TO REASON ABOUT THE RECURSION AT ALL — AND THIS REFUTES THE
"NEEDS A DEEP INDUCTION" SIZING INSTINCT.** Measured 2026-08-29 closing
`Nat.even_xor`, which TWO prior sizings — a lane's handoff and `xor.rs`'s own
module doc — called out of reach, needing machinery "well beyond defining
xor".

It took one unfold. The goal constrains only the **low bit** of `xor m n`,
and that survives exactly one step of `bitwiseAux`'s recursor; the
higher-order recursive term underneath never has to be related to anything,
because `mod 2` erases it. Admitted axiom-free.

So before budgeting an induction, ask: **how much of the recursive value does
the goal actually mention?** If it is a bounded projection — a low bit, a
parity, a residue, a head element — unfold once, erase the tail, and check
whether the obligation is already discharged. The instinct to match the
recursion's depth to the definition's depth is what made two independent
readers oversize this.

Note the shape of the counter-example this does NOT cover: `lt_xor_cases`
stayed open in the same lane, because a highest-differing-bit statement
mentions an **unbounded** part of the value and the technique gives no
foothold.


## No fuel encoding can be a dependent recursor

**NO FUEL ENCODING CAN BE A DEPENDENT RECURSOR, AND THAT PERMANENTLY DECIDES
A WHOLE CLASS OF `ml430` MIRRORS.** Measured 2026-08-29 building
`Nat.binaryRec`. Mathlib's (`Mathlib/Data/Nat/BinaryRec.lean:88` at the pinned
commit `c5ea0035…`) is well-founded recursion on a `log2` measure with a
**dependent** `{motive : Nat → Sort u}`. Ours is structural recursion on a
fuel counter with a motive **constant in `n`**, plus an extra fuel argument
whose recursive equation must be *proved* rather than obtained definitionally.

**The non-dependence is FORCED, not a shortcut.** A fuel-exhaustion row has to
return a value for an arbitrary `n`, and the only thing in hand at that point
is `motive 0`. So no amount of care makes a fuel encoding into Mathlib's
construction.

**CORRECTION, SAME DAY: I GENERALISED THIS TOO FAR AND IT IS FALSE.** I wrote
that "any `ml430` mirror whose Mathlib definition is `WellFounded.fix` with a
dependent motive stays open on this route, however much infrastructure gets
built." **This kernel HAS `WellFounded.fix.{u,v}`** — universe-polymorphic,
with a checked `WellFounded.fix_eq` unfolding theorem (`prelude.rs:215`) —
and it is already used by `gcd`, `bezout_witnesses`, `modeq` and `wilson`.
A lane closed `F:ml430-nat-base-induction` with it on 2026-08-29, against a
genuine `P : Nat → Prop` motive parameter.

What is true is only the narrow claim: **a FUEL encoding's non-dependence is
forced.** The `binaryRec` lane chose fuel; it was not obliged to.

**AND MY REPAIR OF THAT OVER-GENERALISATION WAS ITSELF WRONG, IN BOTH HALVES.
Measured 2026-08-30 (ADR-0840).** I wrote that
`F:ml430-nat-fastfib-eq-cde11774` is "blocked on a `binaryRec` built the
well-founded way rather than the fuel way, which is ordinary work", and put
that into a lane brief. The lane checked it and refuted both parts:

- Mathlib's `fastFibAux` only ever instantiates `binaryRec` at a
  **non-dependent** motive, so the **fuel `binaryRec` already in the tree is
  sufficient**. No well-founded rebuild is needed for this target.
- It would not matter if it were, because **`Nat.fib` ITSELF is a second,
  independently divergent construction**: ours is
  `Nat.fib n := fibAux n 0 1`, a curried-accumulator recursion
  (`nat_prelude/fibonacci.rs`, motive `Nat → Nat → Nat`), against Mathlib's
  own recurrence. Verified by reading the module doc, not inferred.

So the mirror stays open **regardless of effort**, and it is a mirror-flip
question rather than a construction task. **A flip needs EVERY constituent
construction in the statement to match, not just the outermost one** — that
is the generalisable rule, and it is what both my sizings missed. ADR-0840
carries the corrected plan.

Three sizings of one target, by three readers, each wrong in a different
direction. The file that records obstacles accumulates stale ones by
construction, and its authority is exactly what makes them expensive — which
this entry now demonstrates about itself twice over.

This is the standing "do not generalise a lane's local finding" failure in
its purest form: the lane reported accurately on *its own construction*, and
I promoted that into a claim about the whole route. Before writing "cannot be
done here", check whether the kernel already has the primitive. This is the `multichoose`/`minFac` side of the
mirror-flip criterion, arriving from the recursion principle rather than from
the algorithm.

Also measured there, and general: **`Prod` does not exist in this kernel.**
The complete inductive list is `True/False/And/Or/Iff/Eq/Exists/Acc/Bool/Nat/
Decidable` + `Nat.le` + `Nat.Fin` + `Char` (plus `Nat.Pair`, added by that
lane). Every other `Prod` hit is a test fixture or a doc comment recording its
absence. The prelude's standing workaround for a pair is a **`Bool`-selected
function** (`Nat.xgcdAux (sel : Bool)`, `Nat.divModState`, `creal/ivt.rs`'s
`Bool → CReal`) — deliberate, and documented at those sites.

One defect that class of work reliably produces, invisible to `cargo check`:
`NatOps::congr` states its conclusion at `Nat`, so rewriting a component of a
value in ANOTHER type gives `expected: AxNat, got: AxNat.Pair`. The fix is a
`congr_nat_to` keeping the hypothesis at `Nat` and moving only the motive's
body. Anyone building over `Nat.Pair`, `Nat.Fin` or `CReal` will hit it.


## The dev-helper layer hardcodes a carrier

**THE DEV-HELPER LAYER HARDCODES A CARRIER, AND EVERY CROSS-CARRIER USE FAILS
AS ONE OPAQUE `TypeMismatch` ACROSS THE WHOLE SUITE.** Three separate lanes
hit this on 2026-08-29, in three different helpers:

- `NatOps::congr` states its conclusion at `Nat`, so rewriting a component of
  a value in another type gives `expected: AxNat, got: AxNat.Pair`. The
  `Nat.Pair` lane needed a `congr_nat_to` that keeps the hypothesis at `Nat`
  and moves only the motive's body.
- The same defect for `Bool`: the `xor_assoc` lane had to build
  `congr_bool_to_nat` for exactly the same reason.
- `IntDev::irefl` is the **Int-typed** `Eq.refl`. Applied to a `Nat`-sorted
  term it made EVERY `int_prelude` test fail with one `TypeMismatch`; the fix
  was `d.refl`, the `NatOps` trait's Nat-level reflexivity.

None of the three is visible from the call site — the helper name says
`congr` or `refl`, not `congr_at_Nat`. **Before using a dev helper on a term
whose carrier is not the module's own, check what carrier the helper states
its conclusion at.** A tiny `expected` `ExprId` (single digits) means the
kernel wanted a SORT; a mismatch between two large ids in a module that only
touches one carrier usually means this instead.

All three were isolated the same way, and it is the standard move: a
throwaway `#[cfg(test)] mod debug_probe` built against a prelude with the new
declarations disabled, running `Kernel::infer` on each intermediate. Five
lanes used it that day rather than reading a poisoned-prelude failure across
every test in the suite.


## A prelude can declare into another prelude's namespace

**A PRELUDE CAN DECLARE INTO ANOTHER PRELUDE'S NAMESPACE, SO "IS THIS NAME
TAKEN?" IS NOT ANSWERED BY READING THE MODULE IT BELONGS IN.** Measured
2026-08-25: a lane built an explicit inverse for a bijection on `[0,n)` and
named it `Nat.inverseIndex`. That name was already owned by
`int_prelude/wilson.rs`, which declares `Nat.inverseIndex` and eight lemmas
about it into the **`Nat`** namespace from the **Int** prelude — the modular
inverse index from Wilson's theorem, an unrelated function.

Three things made it expensive, and they compound:
- Nothing in `nat_prelude/` mentions the name. The lane was told to check for
  an existing inverse, did, and looked where the code lives.
- **The nat prelude builds fine alone.** `cargo test --lib nat_prelude::` was
  **66 green with the collision present.** It fires only once a downstream
  prelude builds on it.
- The message names neither the string nor either site: `the Int model must
  build: DeclarationExists { name: NameId(457) }`, across **230** failures in
  `arith_model` and `characterization`, none of which mention `Nat` or the
  file that added it.

So before naming a declaration, check the **whole** inventory
(`prelude_theorem_inventory --include-constructed`, `--release`), not the
module you are writing in. And note the asymmetry when you find a clash: the
older declaration is usually load-bearing elsewhere, so rename the NEW one.


## `UnboundFVar` names nothing — write a tree-walk

**`UnboundFVar` NAMES NOTHING, AND THE FIX IS A TREE-WALK YOU CAN WRITE IN ONE
FUNCTION.** `pi_fv` versus `d.arrow` is a recurring trap: a hypothesis whose
fvar the CONCLUSION mentions must bind with `pi_fv`, because `arrow` is
non-dependent and leaves the variable free. The kernel then rejects with a
bare `UnboundFVar` that names neither the binder nor the offending hypothesis.

Measured 2026-08-27 on `integral_by_parts`: **five of seven** hypotheses were
wrong, each referenced by value inside the conclusion's embedded integral and
uniform-continuity witnesses. Rather than bisecting, the lane wrote a
**temporary tree-walk that scanned the built term for free-variable leaks
before calling `add_declaration`**, which pinpointed all five in ONE run; it
then removed the diagnostic and the second attempt succeeded.

Do that instead of bisecting. The scan is cheap, it is exhaustive where a
bisect is serial, and it turns an error that names nothing into a list of
exactly which binders are wrong.


## A sort error arrives wearing a `TypeMismatch`'s clothes

**A SORT ERROR ARRIVES WEARING A `TypeMismatch`'s CLOTHES, and the tell is a
tiny `expected` id.** Measured 2026-08-27: a constant function built with a
`CReal` binder where `sumRange` needs `Nat -> CReal` reported
`TypeMismatch { expected: ExprId(3), got: ExprId(1503219) }` -- naming neither
the lambda nor `sumRange`. **A sort lives at a single-digit `ExprId`**, so an
`expected` in the low single digits means the kernel wanted a SORT and you
handed it a term (or the binder's domain is wrong), not that two elaborate
types disagree. Check the binder before diffing the types.


## `AxNat` is not an axiomatized `Nat`

**`AxNat` IS NOT AN AXIOMATIZED `Nat` — the `Ax` is *axeyum*, and the prefix
means the opposite of what it means in `AxReal`.** Every rendered type in this
kernel prints the naturals as `AxNat`: `AxNat.sumRange`, `AxNat.injectiveOn`,
`Eq.{1} AxNat`. That is `lean_pp`'s non-shadowing root for the kernel's
**computational, inductive, constructed** naturals, chosen so an exported term
does not collide with Lean's own `Nat`, and `nat` measures **0** — no `Axiom`,
no `Opaque`, no `Quotient`.

In `AxReal` the same prefix does mean axiomatized, and that package is this
repository's only nonzero row at **30**. So the two names differ by one letter
and disagree about the headline metric, and a reader who sees `AxNat` in a
pinned type and infers an assumed carrier has axiom-freedom exactly backwards.

The rule this generalizes: **read a carrier's trusted surface from
`Kernel::axiom_footprint`, never from its rendered name.**
`nat_axiom_inventory` covers `nat`/`logic`; `prelude_theorem_inventory
--include-constructed` lists every declared name with its footprint. And note
that `lean_pp` rewrites names on export for two reasons at once — the other is
that a numeric component becomes `_0`, since `foo.0` parses as a projection —
so matching display names against module text reports "not covered" for
artefacts that are perfectly correct.


## `AxReal` and `CReal` are different things

**`AxReal` and `CReal` are different things and one is a substring of the
other.** `CReal` is the CONSTRUCTED reals — a Bishop setoid over the
constructed rationals, trusted surface 0 (ADR-0512) — and it is what the
shipped route actually reasons over. `AxReal` is the legacy AXIOMATIZED
ordered-field package, and it is the repository's only nonzero row:
`axreal: axiom=30`. Every other prelude — `logic`, `nat`, `integer`, `rat`,
`creal`, `complex`, `string` — measures 0.

**The prelude key was `real` until 2026-08-19, and the rename was half-done for
a day.** ADR-0522 renamed the declarations `Real.*` → `AxReal.*`, but the
ledger still filed them under prelude `real`, so the table a referee reads said
`real 30` about 30 rows all named `AxReal.…` — the label contradicting its own
contents, and inviting precisely the reading the rename existed to prevent
("their reals cost 30 axioms", when the reals are `creal` at 0). Both halves
are landed now. Do not reintroduce `real` as a prelude label; the generated
ledger carries a paragraph saying what `axreal` is, and `EXPECTED_PRELUDES`
in `scripts/gen-lean-axiom-ledger.py` is the list a new one must join.

A `contains("Real.")` test matches `CReal.` too, and that has already been hit
and worked around locally (`examples/front_door_carrier.rs:169` decides the
carrier from the carrier DECLARATION for exactly this reason). The same hazard
bit the ledger's own prose scanner: `real (\d+), integer (\d+), string (\d+)`
matched inside "creal 0, integer 0, string 0" — an ordinary sentence now that
the constructed carrier is the one at zero — and scored it against `axreal`,
so a document stating the counts CORRECTLY would have redded the gate. Fixed
with a `(?<![A-Za-z])` lookbehind and controlled both ways in
`scripts/tests/test_lean_axiom_ledger.py`. Decide which package you mean by
its declaration, never by a substring; if you must match text, anchor it.

**Declared is not reached by the DEFAULT route, and both numbers are
published** (ADR-0509). The 30 are declared; the default reconstruction does
not reach them — `Lra`, `DisjunctiveLra`, `Sos` and `IntFarkas` all
reconstruct over constructed carriers. So "we have 30 axioms" and "our proofs
rest on 30 axioms" are both wrong: the first ignores that the shipped route
does not reach them, the second is simply false. Quote the pair.

**"No route reaches them" is too strong, and a lane that reads it that way
will distrust a correct measurement.** One route deliberately does, and
measured 2026-08-27 it is live and green:

    cargo run --release -p axeyum-solver --features full \
      --example infeasibility_farkas_lean -- \
      artifacts/instances/infeasibility/schedule-deadline.smt2 \
      --require-kernel --expect-axioms 26
    ->  kernel-lean route   REACHED (term infers to False)
        kernel axioms       26 = 17 prelude + 4 variable + 5 hypothesis
        axiom-free          no -- the ordered field and every core row are asserted

Nothing about that is a leak, and every part of it is opt-in and loud:
`examples/infeasibility_farkas_lean.rs:292` calls
`LraReconstructCtx::new_over_axreal()` — a constructor NAMED for the choice it
makes, which is ADR-0605's fix for a plain `new()` that used to make it
silently. `prove_unsat_to_lean_module` stopped routing pure-AxReal on
2026-08-15. The tool prints `axiom-free no` itself, and the fact
`F:schedule-critical-chain-infeasible` publishes all 26 in its
`axiom_footprint` with a `--expect-axioms 26` checker that fails if the count
moves.

The distinction to carry: **the default route reaches zero; an explicitly
opted-in demonstrator reaches 26 and says so.** Both are true, both are
measured, and only the pair is honest.

The count is not a dial. `Real`'s carrier is opaque, so nothing over it is
definable and every operation and law must be assumed — **30 is the floor for
an axiomatized ordered field**, not a choice. The negative control every
axiom-freedom measurement is read against is now one assumed law over a
CONSTRUCTED carrier (ADR-0515), which is stronger, because that axiom is
provably redundant and the 30 are only relatively consistent.

## You cannot read the kernel's theorem inventory from source text

**You cannot read the kernel's theorem inventory from source text.**
Declarations go through a `.theorem(name, …)` helper taking an interned
`NameId` field, so grepping `.theorem("…")` returns **zero** matches and
`Declaration::Theorem` returns 1 against 119 real theorems. Three separate
counts of this repository's theorems were wrong before anyone built the
environment to look, and one lane built an out-of-tree probe crate to get types
it could have read directly. Use the examples:
`nat_theorem_inventory` (names + canonical types, the paste-into-a-fact form),
`theorem_axiom_footprint` (per-declaration `Kernel::axiom_footprint`, this
kernel's `#print axioms`), `nat_axiom_inventory` (trusted surface).

