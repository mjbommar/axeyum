# ADR-1510: The side condition is coprimality, not primality, and the additive bijection was the thing nobody had built

Status: accepted
Date: 2026-09-02
Index-summary: **Quadratic reciprocity is still NOT proved, and neither is
Eisenstein's lemma.** What lands is ADR-1260's residue 2 plus the piece its
residue 3 was actually short of. Residue 2 — no lattice point on the line —
needs **coprimality, not primality**: ADR-1260 sized it as Euclid's lemma, and
`Nat.gauss_lemma` is Euclid with the primality side condition already dropped,
so `Nat.mul_ne_mul_of_coprime_of_lt` asks for `gcd p q = 1` and never mentions
`PrimeCond`. Residue 3's real gap was not `Int.sumRange` (landed, ADR-1275) and
not the floor family (landed, ADR-1290): it is that Gauss's lemma runs its
bijection **multiplicatively** (`Int.prodRange_permute`) and Eisenstein needs
the **same bijection additively**, which no aggregate in this kernel had.
`Nat.sumRange_permute` and `Nat.sumRange_point_change` land, transported from
`Nat.countRange_permute` by deleting the `bool_select_nat` wrapper — and the
transport runs in that direction, because `countRange_eq_sumRange` is `Eq.refl`
and so counting is the `{0,1}`-valued SPECIAL CASE of summing, not the reverse.
Four declarations, all admitted on the FIRST kernel attempt, all axiom-free.
Index-status: accepted

## Context

ADR-1260 established that Eisenstein's lattice count routes around ADR-1135's
missing-aggregate wall, landed `Nat.countRectangle_partition`, and named three
residues. Two have since closed: residue 1 (the floor-counting family) by
ADR-1290, and the aggregate ADR-1260 called "the real obstruction",
`Int.sumRange`, by ADR-1275.

This lane was briefed to land Eisenstein's lemma (step 1). It did not, and the
first thing to record is what the brief's picture got wrong, because the
correction is the useful part.

**The brief's named prerequisites were stale in the direction that
UNDER-states progress, and its residue list was stale in the direction that
over-states what remains.** Verified in-tree rather than inherited:

| the brief said | measured here |
| --- | --- |
| `Int.sumRange`, `sumRange_add`, `sumRange_congr` "have since landed" | correct — `int_prelude/sum.rs`, nine registered names |
| "the row-count-is-a-floor lemma" is an open residue | **already closed**, ADR-1290, `nat_prelude/floor_count.rs`, three declarations |
| "the `p·y ≠ q·x` side condition, which is Euclid's lemma and cheap" | cheap, yes — but it is **not** Euclid's lemma, it is `Nat.gauss_lemma`, which is strictly weaker in its hypothesis |
| step 1 is blocked on the mod-2 bookkeeping over `Int.sumRange` | the bookkeeping is not the binding constraint; **the additive permutation law is**, and nothing in three ADRs had named it |

That last row is the finding. This is the standing "a handoff's blocked-on is a
claim about one route" failure in a new place: every prior sizing of Eisenstein
described the *arithmetic* — `(a−1)·Σk = p·(F+N) − 2·Σ_neg`, read mod 2 — and
none described the *set-theoretic* step underneath it, which is that the folded
least residues are a permutation of `[1,m]`. Gauss's lemma has needed exactly
that permutation since ADR-1130 and gets it from `Int.prodRange_permute`. A
`sumRange` analogue did not exist in any prelude.

## Decision

### Residue 2 asks for coprimality

```text
Nat.mul_ne_mul_of_coprime_of_lt : ∀ pp q x y,
  Eq (gcd pp q) 1 → Lt 0 x → Lt x pp → Not (Eq (mul pp y) (mul q x))

Nat.mul_succ_ne_mul_succ_of_coprime : ∀ pp q x y,
  Eq (gcd pp q) 1 → Lt (succ x) pp →
  Not (Eq (mul pp (succ y)) (mul q (succ x)))
```

Four lemmas, no induction, no case split: `pp·y = q·x` makes `y` a witness for
`pp ∣ q·x` (`Nat.dvd a n` is `∃ k, n = a·k`, so the witness equation is the
symmetrised hypothesis verbatim and no `dvd_mul`-shaped lemma is needed);
`Nat.gauss_lemma` gives `pp ∣ x`; `Nat.le_of_dvd` with `0 < x` gives `pp ≤ x`;
`lt_of_lt_of_le` and `lt_irrefl` close it.

**Why coprimality is the right hypothesis and not a shortcut.** ADR-1260 wrote
"the proof is `p ∣ q·x` with `p ∤ q` and `x < p`, i.e. Euclid's lemma, which
this kernel has". It has better: `Nat.gauss_lemma` (`lcm.rs`) is
`gcd x y = 1 → x ∣ y·z → x ∣ z`, which its own doc records as "exactly the
`g = 1` branch of `euclid_lemma` with the primality side condition dropped".
Taking `PrimeCond pp` here would make every consumer carry a primality proof
through a step that does not use it, and would leave the (true) statement at
coprime composites unreachable. The law's two primes are distinct, and distinct
primes are coprime, so nothing downstream is harder for it.

**The positivity hypothesis is load-bearing, not decoration.** At `x = 0` the
statement is false — `pp·0 = q·0` — so a version without it cannot be proved and
should not be attempted. The `1`-based corollary exists so that no consumer ever
has to produce it: the rectangle's coordinates are `succ`-shaped by
construction, and `NatOps::zero_lt_succ` discharges the obligation once, here.

**The bound is on `x`, and the asymmetry is real.** `pp·y = q·x` forces
`pp ∣ x`, never `pp ∣ y`. The transposed reading — bound `y` instead — is FALSE
at `(pp, q, x, y) = (5, 3, 5, 3)`: `5·3 = 3·5` with `gcd 5 3 = 1` and
`0 < y = 3 < 5`. The intended theorem does not reach that point (`x = 5` is not
below `pp = 5`), which is precisely why no evaluation test over instances it
DOES reach can see a consistent transposition of the four binders. The declared
types are pinned character for character instead.

### The additive bijection

```text
Nat.sumRange_point_change : ∀ a b i0 n, Lt i0 n →
  (∀ k, Lt k i0 → Eq (a k) (b k)) →
  (∀ k, Lt i0 k → Lt k n → Eq (a k) (b k)) →
  Eq (add (sumRange a n) (b i0)) (add (sumRange b n) (a i0))

Nat.sumRange_permute : ∀ f σ n, InjectiveOn σ n → MapsInto σ n →
  Eq (sumRange f n) (sumRange (fun k => f (σ k)) n)
```

Same hypotheses, same argument order and same `f`-outside / `σ`-generalized
induction as `Nat.countRange_permute` and `Int.prodRange_permute`, deliberately,
so the three read against each other.

**It is not a corollary of the counting version, and the direction is the
point.** `Nat.countRange_eq_sumRange` (ADR-1260) is `Eq.refl`: `countRange f n`
IS `sumRange (fun k => bool_select_nat (f k) 1 0) n`. So `countRange_permute` is
the `{0,1}`-valued special case of `sumRange_permute`. A permutation argument
over a general `Nat`-valued family cannot be recovered from the counting one,
which never sees a summand bigger than `1`.

What the counting proof *does* buy is certainty about the route: it is this
proof with the summand specialized, so every step is known to close, and the
only question is whether deleting the selector loses anything. It does not — no
step used the summand's `Bool`-ness. Each `Eq Bool` hypothesis becomes an
`Eq Nat` one; each `bool_congr_nat`/`nat_congr_bool` becomes the ordinary
`NatOps::congr`; the `bool_select_nat` wrapper disappears from every term. Two
of the counting file's four declarations did not have to be rebuilt at all:
`Nat.sumRange_congr_lt` already existed in `binomial.rs`, and
`Nat.countRange_product` has no bearing here.

**`Int.prodRange_swap` is again avoided.** The counting file records that
`Int.prodRange_permute`'s `i0 < n` branch pays for moving a value from slot `i0`
to slot `n` with an adjacent-transposition induction `wilson.rs` took three
drafts to land. `sumRange` accumulates with `Nat.add`, so the same move is one
point-change lemma. The same relief applies to any future `Nat`-valued fold.

## What this does NOT prove

**Quadratic reciprocity is not proved. Eisenstein's lemma is not proved.
Neither step of Eisenstein's argument is proved.**

What the law still needs, in the order a next lane should attack it, and with
each item verified in-tree rather than inherited from a prior handoff:

1. **The additive Gauss bijection, instantiated.** `Nat.sumRange_permute` is
   general; the consumer needs it at the specific self-map
   `σ j := pred (gaussFold pp a (succ j))`, whose `InjectiveOn`/`MapsInto` on
   `[0,m)` are **already proved and already `Nat`-typed** —
   `Nat.gauss_fold_shift_injective_on` and `Nat.gauss_fold_shift_maps_into`,
   built for `int_prelude/gauss_assembly.rs` and quantified over exactly the
   predicates `sumRange_permute` takes. This is assembly, not new mathematics:
   one `sumRange_congr_lt` moving `succ (σ j)` to `gaussFold pp a (succ j)` via
   `Nat.succ_pred_of_pos` fed by `Nat.gauss_fold_in_range`, exactly as
   `gauss_assembly.rs` does it for the product.
2. **The residue/fold reconciliation.** `leastResidue = gaussFold` when the sign
   is false and `= pp − gaussFold` when it is true, so
   `Σ leastResidue = Σ gaussFold + pp·N − 2·Σ_neg gaussFold` where
   `N = gaussNegCount`. This wants a conditional sum — a `sumRangeIf`-shaped
   aggregate, or the same fold with a `bool_select` summand — and **nothing in
   this ADR checked whether one exists.** `Int.prodRangeIf` does
   (`euler_prod_*`); whether it transports is unmeasured, and this ADR does not
   claim it does.
3. **The mod-2 bookkeeping**, over `Int.sumRange` and `Int.modEq_sumRange`
   (ADR-1275, unconditional in the modulus). This is what every prior sizing
   called the obstruction; on the evidence here it is the last step, not the
   binding one.
4. **Step 2's assembly** — `Nat.countRectangle_partition` (ADR-1260) at the two
   strict predicates, discharging its per-point hypothesis with
   `Nat.mul_succ_ne_mul_succ_of_coprime` (this ADR) and naming the row counts
   as floors with `Nat.countRange_mul_succ_le_eq_floor` (ADR-1290). Every input
   now exists. Nobody has run it.

## Numeric verification

Re-runnable, and **this is the command, not a claim that it passed**:

```sh
python3 docs/research/09-decisions/adr-1510-eisenstein-side-and-sum-permute-checks.py
```

Five claims (C1–C5) and seven controls (M1–M7). C1 sweeps 766,167 `(x,y)`
witnesses over 979 coprime `(p,q)` pairs; C3 checks the consequence step 2
actually needs — that at 40,548 lattice points across every ordered pair of
distinct odd primes below 60, **exactly one** of the two strict half-plane
predicates holds, which is `countRectangle_partition`'s per-point hypothesis
verbatim; C5 checks the permutation law over EVERY permutation of `[0,n)` for
`n ≤ 6` rather than a sample.

Exit status depends on the finding. That claim is itself measured: **11 of 11
mutations of the script exit 1** — each claim inverted, each control's named
witness moved or neutered, and the recorded survivor made to stop surviving.

**M6 is recorded as a deliberate SURVIVOR** and asserted to survive: swapping
`a` and `b` throughout `sumRange_point_change` leaves a TRUE statement, because
the equation `Σa + b i0 = Σb + a i0` is symmetric in that swap. No numeric check
can separate the two readings.

## Mutation table

Each mutation is applied in this lane's own isolated worktree — never the shared
checkout — the `nat_prelude::` sweep is run, and the file is restored in a
`finally` so an interrupt cannot leave a mutant behind.

| mutation | what it changes | outcome | evidence |
| --- | --- | --- | --- |
| K1 | the side condition's bound stated on `y` instead of `x` | **REJECTED** | the prelude build fails, so the whole `nat_prelude::` sweep fails with it -- one bad declaration poisons the shared build, and the failure COUNT says nothing about how many things are broken |
| K2 | the side condition's conclusion sides exchanged (general form only) | **REJECTED** | `TypeMismatch { expected: ExprId(1096188), got: ExprId(1096070) }` |
| K3 | `point_change` with both corrections on the same family (`Σa + a i0 = Σb + b i0`) -- a FALSE statement | **REJECTED** | the prelude build fails |
| K4 | `sumRange_permute`'s conclusion sides exchanged (true, and not the theorem) | **REJECTED** | the prelude build fails |
| K5 | `point_change`'s two family binders in the opposite order, consistently in type and value | **REJECTED** | `TypeMismatch { expected: ExprId(1105631), got: ExprId(1105683) }` |

**K5 is the one worth reading, and it did not do what it was designed to do.**
It was built to be this file's *admitted-true-not-your-theorem* case — the
mirror of ADR-1260's M4, where swapping two binders gives a true theorem the
kernel happily admits. It was REJECTED instead, and **not because the swapped
statement is false**: it is true, and on its own it would be admitted. It fails
because `sumRange_permute` CONSUMES it, applying it at `f ∘ τ` on the left and
`f ∘ σ` on the right and then rewriting only the left index. The consumer pins
the argument order that the statement alone does not.

So this table contains **no instance of an admitted-and-surviving mutant**, and
that is a gap, not a strength: the survivor exists (ADR-1510's M6 shows the swap
is true numerically), it is simply masked here by a consumer that happens to
exist today. Were `sumRange_point_change` to be landed without
`sumRange_permute` above it, the same mutation would survive and only the pinned
declared type would catch it. That is why the type is pinned.

**Also not covered:** every guard in this table is on the DECLARATION. Nothing
mutates the `theorem_names` registration, and if a name were dropped from it,
`every_nat_declaration_is_checked_and_axiom_free` would catch it — measured,
because that assertion fired on both `eisenstein_side.rs` names and both
`sum_range_permute.rs` names on their first run and had to be satisfied by
registering them.

## Verification

- `cargo test --release -p axeyum-lean-kernel --lib -- nat_prelude::` —
  **335 passed, 0 failed**, including
  `every_nat_declaration_is_checked_and_axiom_free`, which reads
  `kernel.environment()` rather than a literal list.
- `cargo test --release -p axeyum-lean-kernel --lib -- int_prelude::` —
  **74 passed, 0 failed** (the downstream prelude builds on this one).
- `cargo clippy --release -p axeyum-lean-kernel --lib --all-targets -- -D warnings`
  — clean.
- `python3 docs/research/09-decisions/adr-1510-eisenstein-side-and-sum-permute-checks.py`
  — PASS, and 11 of 11 self-mutations exit 1.
- `python3 scripts/validate-facts.py` — **2580 facts, 0 errors**.
- Both fact `checker_command`s were run with a negative control:
  `theorem_dependency_inventory` piped to an anchored `grep -c` prints `1` and
  exits 0 for a real name, and prints `0` and exits **1** for a name with one
  character changed.

## What the controls do NOT catch

1. **Nothing here constructs a `PrimeCond` proof, and nothing needs to** — the
   side condition has no primality hypothesis. But it means the tests say
   nothing about whether a CONSUMER can produce `gcd p q = 1` for two distinct
   odd primes. `Nat.coprime_primes` exists (`primes.rs`); it was not exercised.
2. **The instantiation tests supply the permutation hypotheses as opaque free
   variables.** Building `InjectiveOn`/`MapsInto` for a concrete reversal is a
   case split over three indices that says nothing about the theorem, so the
   check is that the inferred CONCLUSION is the intended equation, plus separate
   evaluation of both its sides. A theorem with the right conclusion and wrong
   hypotheses would pass that pair; the declared type pin is what catches it.
3. **`Nat.sumRange_congr_lt` is reused, not re-derived, and its own correctness
   is inherited.** It came from `binomial.rs` and this lane added no test for
   it.
4. **The `succ` corollary is checked at two prime pairs, `(3,5)` and `(5,7)`.**
   The 979-pair sweep is in Python, outside the kernel.
5. **Nothing measures whether residue 2's statement is the shape step 2's
   assembly will actually want.** C3 checks that the complementarity FOLLOWS
   from it numerically; no kernel term connects the two, and this ADR does not
   claim one is easy.

## Consequences

- `Nat.sumRange_permute` and `Nat.sumRange_point_change` have no connection to
  reciprocity. Anything folding a `Nat`-valued family over `[0,n)` under a
  reindexing can use them, and the point-change law is the general relief from
  `prodRange_swap`-style transposition inductions for any additive aggregate.
- `Nat.mul_ne_mul_of_coprime_of_lt` likewise mentions no primes and no lattice.
  It is the statement "a coprime pair's multiples never collide below the
  modulus", which is the same content `Nat.least_residue_injective_of_coprime`
  uses in a different form.
- The retrieval lesson, since this file collects them: **when a triage reports
  an argument blocked, ask which OTHER aggregate in this development already
  runs the same argument.** Gauss's lemma has run this exact bijection since
  ADR-1130 — over `Int.prodRange`, in the `Int` prelude, under a name
  (`prodRange_permute`) no `sumRange` query reaches. That is the sixth entry in
  CLAUDE.md's hiding-place taxonomy, hit again, by a lane that had read it.
