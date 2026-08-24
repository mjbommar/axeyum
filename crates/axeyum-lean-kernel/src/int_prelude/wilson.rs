//! `Int.factorial`, the self-inverse analysis Wilson's theorem needs, and
//! `Int.factorial_pos` — the assembly slice toward Wilson's theorem
//! (`p` prime ⟹ `(p-1)! ≡ -1 [p]`). Also, since 2026-08-24, the coprime form
//! of Fermat's little theorem (`Int.pow_prime_sub_one_modeq_one`,
//! `p ∤ a ⟹ a^(p−1) ≡ 1 [p]`) and its bridging lemma `Int.of_nat_pow`; and,
//! later the same day, the *executable* modular inverse this whole chain was
//! built to reach — `Int.mul_inv_of_pow`, `Nat.inverseIndex`, its
//! permutation proof `Nat.inverseIndex_maps_into` /
//! `Nat.inverseIndex_injective`, the fixed-point characterisation that
//! decides Wilson's sign — `Nat.inverseIndex_fixed_point` — and, still later
//! the same day, `Nat.inverseIndex_involutive` (`σ` is its own inverse),
//! landed as the missing linchpin the interior-collapse induction needs (see
//! "What Wilson is blocked on now", below).
//!
//! ## What lands here, and what does not
//!
//! `Int.factorial` (a `prodRange` instance) and `Int.self_inverse_mod_prime`
//! (the genuinely prime-theoretic heart: `a*a ≡ 1 [p]` forces `a ≡ ±1 [p]`,
//! via `Int.euclid_lemma` deciding which factor of `(a-1)(a+1)` `p` divides —
//! a real constructive disjunction, not excluded middle) are both proved
//! here, axiom-free. So is `Int.pow_prime_sub_one_modeq_one`
//! (`declare_pow_prime_sub_one_modeq_one`, below) — the headline form of
//! Fermat every application actually wants, as opposed to the unrestricted
//! `Nat.pow_prime_modeq_self : prime p → a^p ≡ a [p]` this whole chain rests
//! on.
//!
//! ## The executable inverse, landed 2026-08-24
//!
//! To use `prodRange_permute` the pairing needs a **concrete `σ : Nat → Nat`**
//! — the `injectiveOn`/`mapsInto` predicates quantify over a function, not
//! over a proof that one exists, and `Int.gcd_eq_gcd_ab`/`Nat.gcd_bezout`
//! cannot supply it: their witnesses are `Prop`-level existentials,
//! extracted by `exists_elim` *inside* a proof, and a `Prop`-level
//! existential does not eliminate into a `Type` target (the same wall
//! `CReal.inv` and `pos_bound_of_lt` hit). The Fermat route can, because
//! `σ(k) := a^(p-2) mod p` is closed form, and every piece it needs is now
//! landed:
//!
//! - `Int.mul_inv_of_pow` (`declare_mul_inv_of_pow`) — one more split of
//!   `Int.pow_prime_sub_one_modeq_one`: `a^(p-1) = a^(p-2)·a` via
//!   `Int.pow_succ` and `succ(p-2) = p-1` (two `Nat.sub_add_cancel`s glued by
//!   `Nat.succ_injective`), giving `a · a^(p-2) ≡ 1 [p]`.
//! - `Nat.inverseIndex` (`declare_inverse_index`) — the checked `Definition`
//!   `fun p k => natAbs (emod (pow (ofNat (succ k)) (p-2)) (ofNat p)) - 1`.
//! - `Nat.inverseIndex_maps_into` — `Int.emod` always lands in
//!   `[0, ofNat p)`, and that bound transports to `ℕ` for free: `Int.lt` on
//!   two `ofNat`-headed arguments reduces *structurally* to `Nat.lt`
//!   (`int_prelude/defs.rs`'s four-case table), so no separate
//!   order-transfer lemma was needed. The closing `- 1` (truncated
//!   `Nat.sub`) needs a case split on whether the residue is `0`, not a
//!   proof that it never is — `Nat.lt_or_eq_of_le` covers both outcomes.
//! - `Nat.inverseIndex_injective` — the harder half: does need the residue
//!   to be nonzero (`mag_ne_zero`, a local helper — if it were `0`,
//!   `mul_inv_of_pow` plus `Int.emod` being the identity on `0` and `1`
//!   (`emod_eq_self_of_in_range`, another local helper, built from
//!   `Int.ediv_emod_unique`) would force `1 = 0`) to cancel the `- 1`
//!   cleanly, then `Int.modEq_inverse_unique` collapses two indices with the
//!   same inverse residue to the same source residue, and
//!   `emod_eq_self_of_in_range` again (this time on the two *sources*, which
//!   are already canonical representatives) turns that congruence into
//!   literal equality.
//!
//! The indexing, settled: `a := ofNat(k+1)` for `k < n` with
//! `n := natAbs(p) - 1`, so `{0,…,p-2}` maps onto `{1,…,p-1}` and `n` is the
//! same `Nat` that `Int.factorial` already consumes for `(p-1)!` — no
//! reindexing gap against the rest of the chain. `p = 2` needed no special
//! case: `p - 2 = 0` exactly (`Nat.sub_add_cancel` applies to the truncated
//! difference the same as any other), and the lone index `k = 0` is covered
//! by exactly the same argument as every other prime.
//!
//! ## The fixed-point characterisation, landed 2026-08-24
//!
//! `Nat.inverseIndex_fixed_point` (`declare_inverse_index_fixed_point`):
//! `p` prime, `k < p-1`, `σ k = k` (`σ := Nat.inverseIndex p`) ⟹ `k = 0 ∨
//! k = p-2` — the converse of the two direct computations `σ 0 = 0` /
//! `σ (p-2) = p-2` (neither is built here; both are immediate unfoldings this
//! development has not needed to name). Equivalently: the only residues that
//! are their own modular inverse are `1` and `p-1`. This is the theorem that
//! says a pairing argument over `σ` has exactly two exceptions, and it is the
//! genuine mathematical content of Wilson's theorem — `Int.self_inverse_mod_prime`
//! (`a*a ≡ 1 [p] ⟹ a ≡ ±1 [p]`, via `Int.euclid_lemma`) transported across
//! the index/residue correspondence `a := ofNat(k+1)`. The transport needed
//! one genuinely new piece: `Int.sub (ofNat p) one = ofNat (p-1)`, built from
//! `Int.add_neg_cancel_right` rather than the `subNatNat` borrow development
//! (`Int.sub` unfolds transparently to `add a (neg b)`, so no case split on
//! the symbolic magnitude is needed — cheaper than reaching for the borrow
//! machinery `sub_nat_nat.rs` built for exactly this kind of question).
//!
//! ## The involution, landed 2026-08-24
//!
//! `Nat.inverseIndex_involutive` (`declare_inverse_index_involutive`):
//! `p` prime, `k < p-1` ⟹ `σ (σ k) = k` (`σ := Nat.inverseIndex p`),
//! unconditionally — no fixed-point hypothesis needed, unlike
//! `inverseIndex_fixed_point`. Built the same way: `Int.mul_inv_of_pow`
//! applied at both `k`'s own residue and its image, glued by
//! `Int.modEq_inverse_unique` (both residues are inverses of the *same*
//! value, hence congruent to each other, hence — being canonical
//! representatives in `[0,p)` — literally equal). This landed on the first
//! attempt, reusing exactly the local helpers (`mag_ne_zero`,
//! `emod_eq_self_of_in_range`, `emod_modeq_self`, the `natAbs`-transparency
//! `refl` trick) `inverseIndex_injective`/`inverseIndex_fixed_point` already
//! established — it turned out to be data-plumbing at the same difficulty as
//! those two, **not** a third difficult induction. It was not on the original
//! plan for this slice; it was discovered to be load-bearing while designing
//! the collapse argument below, and every route to that argument this session
//! explored needed it.
//!
//! ## What Wilson is blocked on now, measured 2026-08-24
//!
//! Every ingredient the permutation argument needs is landed and axiom-free:
//! a concrete `σ := Nat.inverseIndex p`, its `InjectiveOn`/`MapsInto`/
//! involution proofs, its fixed-point characterisation, and
//! `Int.prodRange_permute` itself. What is **not** yet built is the
//! *collapse* argument Wilson's theorem needs on top of the permutation: `σ`
//! pairs each survivor with its distinct inverse, and the fixed-point lemma
//! now says in advance which two indices are their own image under `σ`, but
//! turning "the product over a permuted range, where all but two factors
//! cancel pairwise against their partner" into a closed form is still a
//! genuinely new inductive argument — not a data-plumbing exercise like the
//! pieces above.
//!
//! **This is harder than "a swap/override induction removing one matched
//! pair at a time" made it sound**, and the gap is now measured, not just
//! estimated. `Int.prodRange_permute`'s own induction (`permute_step`,
//! `prod.rs`) removes exactly **one** index per structural step — pigeonhole
//! locates `i0` with `σ i0 = n` (the domain's own top index), and the
//! recursive call is at domain `n` with an *overridden* `τ`, never at domain
//! `n - 1` with `n` and `i0`'s CONTRIBUTIONS actually gone. That machinery
//! provably cannot be reused unchanged: unwinding it all the way down (as
//! this file confirmed by hand-tracing `permute_branch_swap`'s own peeled
//! factor at every level) reconstructs `prodRange F N` from itself term by
//! term — a tautology, because `F` never changes and only `σ` does, so it
//! carries no information about which pairs multiply to `1`. Getting the
//! *sign* (not just the square, which `factorial_sq_modeq_one` already gets
//! for free) genuinely requires removing **two** positions' contributions
//! together, which needs domain `N → N - 2` in one step, not `N → N - 1`.
//!
//! The design that closes that gap, worked out and cross-checked against the
//! existing `prod.rs` machinery this session (not yet built):
//!
//! 1. **Strong induction on the domain size**, via `WellFounded.fix` over
//!    `Nat.lt` exactly as `nat_prelude/gcd.rs`'s `declare_gcd_semantics`
//!    already does to prove `gcd_dvd` (`p.nat.lt_well_founded` +
//!    `p.logic.well_founded_fix`, family `fun n => ∀ F σ, [hyps] → ModEq p
//!    (prodRange F n) 1`, recursive-IH type `∀ m, m < n → family m`) — this
//!    is what makes "recurse at `n - 2`" a single step instead of needing a
//!    second bespoke induction principle.
//! 2. **Global hypotheses, not per-branch ones**: state the lemma for `σ`
//!    fixed-point-free on the *entire* domain (`∀ k < n, σ k ≠ k`) and the
//!    pairwise congruence `∀ k < n, ModEq p (F k * F (σ k)) 1` holding for
//!    *every* `k` (both are what the interior application actually has, via
//!    `inverseIndex_fixed_point`). This removes the "`i0 = n`" fixed branch
//!    entirely — it becomes a one-line `absurd` against the global hypothesis
//!    — leaving only the general case to handle, unlike `permute_step`'s two
//!    real branches.
//! 3. **The `N → N - 2` step, using the involution**: pigeonhole for the
//!    *preimage* of the top index is not needed — `inverseIndex_involutive`
//!    means the top index `n - 1`'s partner is `i0 := σ (n-1)` directly, and
//!    `σ i0 = n - 1` for free (no separate search). If `i0 = n - 2`, peel the
//!    last two factors off `prodRange F n` directly (two `prodRange_succ`
//!    unfoldings) — their product is `F(n-2) * F(σ(n-2)) = F(n-2)*F(n-1) ≡ 1`
//!    by involution (`σ(n-2) = σ(σ(n-1)) = n-1`) — and the IH applies to
//!    `prodRange F (n-2)` with the *same* `F` and `σ` (restricted; injectivity
//!    alone forces nothing else maps into `{n-2,n-1}`, since `σ` already maps
//!    both of them there). Otherwise (`i0 < n-2`), conjugate `σ` by the
//!    transposition `τ := (i0, n-2)` (`prod.rs`'s existing `point_swap`
//!    machinery builds `τ` and its case-equalities already): `σ' := τ∘σ∘τ`.
//!    Involution makes `σ'` fix `{n-2,n-1}` **setwise**
//!    (`σ'(n-2)=n-1,σ'(n-1)=n-2`, a two-line computation from `σ(n-1)=i0` and
//!    `σ(i0)=n-1`), which is exactly what licenses restricting `σ'` to
//!    `[0,n-2)`; and `H := F∘τ` (via `Int.prodRange_swap`, already landed,
//!    giving `prodRange F n = prodRange H n` exactly) satisfies `H(k)*H(σ'
//!    k) = F(τ k)*F(σ(τ k))` — the *original* pairwise hypothesis at `τ k` —
//!    so the recursive call is `IH` at `(n-2, H, σ')`.
//! 4. **What step 3 still needs, unbuilt**: (a) the "conjugating an
//!    `InjectiveOn`/`MapsInto` self-map by a transposition preserves both"
//!    lemma (standard, but not present — `Nat.restrict_injective`/
//!    `restrict_maps_into` are built for *removing the top index via
//!    override*, a different operation, not reusable here without
//!    adaptation); (b) "a bijection of `[0,n)` fixing a two-element subset
//!    setwise restricts to a bijection of the complement" (also standard, also
//!    not present); (c) that global fixed-point-freeness transports through
//!    conjugation (needs its own short case split); (d) the interior
//!    application's *own* setup — showing the shifted `σ` is fixed-point-free
//!    and `InjectiveOn`/`MapsInto` on the interior domain specifically needs
//!    `σ 0 = 0` and `σ (p-2) = p-2` as *equations*, which this file's own
//!    comments have twice noted are "immediate unfoldings this development
//!    has not needed to name" — they still are not named. None of (a)–(d) is
//!    large individually, but together they are comparable in size to
//!    `Nat.restrict_injective`/`restrict_maps_into` combined, i.e. a second
//!    substantial induction-adjacent development, not a short follow-up.
//!
//! Wilson's theorem itself is **not** declared here — that is its own slice —
//! but the rearrangement principle
//! it needs is now fully proved and axiom-free: `Int.prodRange_permute`
//! (`prod.rs`) : `∀ f σ n, InjectiveOn σ n → MapsInto σ n →
//! prodRange f n = prodRange (fun k => f (σ k)) n`. The classical proof of
//! Wilson's theorem collapses `prodRange` over `2..p-2` by pairing each
//! survivor with its distinct inverse — a permutation argument — and
//! `prodRange_permute` is exactly the rearrangement step that argument needs:
//! `Int.prodRange : (Nat → Int) → Nat → Int` folds over a fixed *initial
//! segment* `{0,…,n-1}`, so reasoning about "the product over the remaining
//! unpaired elements" has to go through a `σ` that moves each survivor's
//! partner into its slot, and `prodRange_permute` is what licenses that move
//! for an arbitrary `InjectiveOn`/`MapsInto` self-map, not just one swap.
//!
//! It was built in three stages, the last landing 2026-08-24:
//! `Nat.Fin`, `Nat.injectiveOn` / `surjectiveOn` / `mapsInto`, and the
//! pigeonhole principle connecting them
//! (`Nat.injective_on_imp_surjective_on`, `nat_prelude/finite.rs`);
//! `Int.prodRange_swap_adjacent` (one adjacent transposition) and
//! `Int.prodRange_swap` (any two indices `i < j`, via `prod.rs`'s
//! `point_swap` — a `Nat.ble`-cascaded explicit swap function, never
//! `Nat.beq` — and a conjugation induction `(j' j)(i j')(j' j) = (i j)` on the
//! gap `j - i`); and finally `prodRange_permute` itself, induction on `n`
//! with `f` quantified OUTSIDE the `Nat.rec` and the motive generalized over
//! **`σ`, not `f`** (motive `∀ σ, injectiveOn σ x → mapsInto σ x →
//! prodRange f x = prodRange (f ∘ σ) x`; three earlier drafts generalized over
//! `f` instead, copying every earlier proof in this chain, and that shape does
//! not close — the recursive call here reuses the same `f` and only `σ`
//! changes). At `n+1` the pigeonhole locates `i0 < n+1` with `σ i0 = n`: the
//! `i0 = n` branch is pure bound-weakening (`σ` already fixes `n`), and the
//! `i0 < n` branch applies `point_swap` to `g := f ∘ σ` at `(i0, n)` — not to
//! `σ` — reducing the recursive obligation to `prodRange (f ∘ τ) n =
//! prodRange f n` for the OVERRIDE `τ := point_override σ i0 (σ n)` (never a
//! downward reindex: once `i0 = n` is peeled off, `i0` is already `< n`, so
//! there is nothing to shift), with `Nat.restrict_injective` /
//! `Nat.restrict_maps_into` (`nat_prelude/finite.rs`) supplying `τ`'s two
//! closure properties.

use super::defs::POW_HEIGHT;
use super::ops::IntDev;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// Delta height for `Int.factorial`, which calls `Int.prodRange` (itself
/// `POW_HEIGHT + 1`, `prod.rs`'s private `PROD_RANGE_HEIGHT`); strictly
/// greater so unfolding order stays fixed.
const FACTORIAL_HEIGHT: u16 = POW_HEIGHT + 2;

/// Admit `Int.factorial : Nat → Int := Int.prodRange (fun k => Int.ofNat (Nat.succ k))`.
///
/// Mirrors `Nat.factorial`'s own convention exactly (`nat_prelude/defs.rs`):
/// the new factor is multiplied onto the **right** of the prior product, so
/// `factorial (succ n) ≡ factorial n * ofNat (succ n)` — the same shape as
/// `Nat.factorial (succ n) ≡ factorial n * succ n`, transported to `ℤ`.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated definition does not
/// type-check or the name is already taken.
pub(super) fn declare_factorial(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();

    // f := fun (k : Nat) => Int.ofNat (Nat.succ k)
    let f = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let body = d.of_nat(sk);
        d.lam_fv(k_fv, nat, body)
    };
    let prod_range = d.kernel().const_(p.prod_range, vec![]);
    let value = d.apply(prod_range, &[f]);
    let ty = d.arrow(nat, int_ty);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.factorial,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(FACTORIAL_HEIGHT),
    })
}

/// `factorial_zero : Eq Int (factorial zero) one` and
/// `factorial_succ : ∀ n, Eq Int (factorial (succ n)) (mul (factorial n) (ofNat (succ n)))`.
///
/// Both close by `Eq.refl` alone: `Int.factorial` unfolds to `Int.prodRange f`
/// for a fixed `f`, and `prodRange`'s own defining equations
/// (`prod.rs::declare_prod_range_equations`) are themselves `Eq.refl` proofs,
/// so the composition reduces all the way through with no rewrite needed —
/// the same signal `prodRange_zero`/`prodRange_succ` report for
/// `Int.prodRange` itself.
///
/// # Errors
///
/// Returns the trusted gate's rejection if a generated proof does not check.
pub(super) fn declare_factorial_equations(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();

    // factorial_zero : Eq Int (factorial zero) one
    {
        let zero = d.zero();
        let lhs = d.const_app(p.factorial, &[zero]);
        let one = d.ione();
        let stmt = d.ieq(lhs, one);
        let proof = d.irefl(one);
        d.declare_theorem(p.factorial_zero, stmt, proof)?;
    }

    // factorial_succ :
    //   ∀ (n : Nat), Eq Int (factorial (succ n)) (mul (factorial n) (ofNat (succ n))).
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let lhs = d.const_app(p.factorial, &[sn]);
        let prior = d.const_app(p.factorial, &[n]);
        let sn_i = d.of_nat(sn);
        let rhs = d.imul(prior, sn_i);
        let stmt = d.ieq(lhs, rhs);
        let proof = d.irefl(rhs);

        let ty = d.pi_fv(n_fv, nat, stmt);
        let value = d.lam_fv(n_fv, nat, proof);
        d.declare_theorem(p.factorial_succ, ty, value)?;
    }
    Ok(())
}

/// `2 ≤ magnitude ∧ ∀ (x : Nat), x ∣ magnitude → Eq Nat x 1 ∨ Eq Nat x magnitude` —
/// the same inline primality convention `Int.euclid_lemma` uses (this
/// prelude has no `Prime` name over either carrier). Spelled out again here
/// rather than imported: `gcd.rs`'s copy (`int_prime_condition`) is not
/// `pub(super)`, and this is five lines.
fn prime_condition(d: &mut IntDev<'_>, magnitude: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let two_nat = d.num(2);
    let one_nat = d.num(1);
    let two_le = d.le(two_nat, magnitude);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hyp = d.dvd(x, magnitude);
    let is_one = d.eq(x, one_nat);
    let is_whole = d.eq(x, magnitude);
    let disjunction = d.or(is_one, is_whole);
    let inner = d.arrow(hyp, disjunction);
    let clause = d.pi_fv(x_fv, nat, inner);
    d.and(two_le, clause)
}

/// `Eq Int (mul (sub a one) (add a one)) (sub (mul a a) one)` — the
/// difference of squares `(a-1)(a+1) = a*a - 1`.
///
/// Expansion: commute to `(a+1)*(a-1)`, distribute the subtraction via
/// `mul_sub`, expand `(a+1)*a` via `mul_comm`/`left_distrib`/`mul_one` into
/// `a*a+a`, collapse `(a+1)*1` to `a+1` via `mul_one`, commute that `a+1` to
/// `1+a`, and finish with
/// [`super::modeq::cancel_common_addend`]`(a*a, one, a)`, which is exactly
/// the `(X+r)-(Y+r) = X-Y` shape the last step needs.
fn diff_of_squares(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let p = d.int();
    let one_i = d.ione();
    let aa = d.imul(a, a);
    let sub_a1 = d.isub(a, one_i);
    let add_a1 = d.iadd(a, one_i);
    let diff = d.isub(aa, one_i);

    let start = d.imul(sub_a1, add_a1);

    // (a-1)*(a+1) = (a+1)*(a-1)
    let t1 = d.imul(add_a1, sub_a1);
    let p1 = d.const_app(p.mul_comm, &[sub_a1, add_a1]);

    // (a+1)*(a-1) = (a+1)*a - (a+1)*1
    let m_add_a = d.imul(add_a1, a);
    let m_add_one = d.imul(add_a1, one_i);
    let t2 = d.isub(m_add_a, m_add_one);
    let p2 = d.const_app(p.mul_sub, &[add_a1, a, one_i]);

    // (a+1)*a = a*(a+1)
    let m_a_add = d.imul(a, add_a1);
    let t3 = d.isub(m_a_add, m_add_one);
    let p3_eq = d.const_app(p.mul_comm, &[add_a1, a]);
    let p3 = d.icongr(m_add_a, m_a_add, p3_eq, &|d, t| d.isub(t, m_add_one));

    // a*(a+1) = a*a + a*1
    let a_one = d.imul(a, one_i);
    let sum4 = d.iadd(aa, a_one);
    let t4 = d.isub(sum4, m_add_one);
    let p4_eq = d.const_app(p.left_distrib, &[a, a, one_i]);
    let p4 = d.icongr(m_a_add, sum4, p4_eq, &|d, t| d.isub(t, m_add_one));

    // a*1 = a
    let sum5 = d.iadd(aa, a);
    let t5 = d.isub(sum5, m_add_one);
    let p5_eq = d.const_app(p.mul_one, &[a]);
    let p5 = d.icongr(a_one, a, p5_eq, &|d, t| {
        let s = d.iadd(aa, t);
        d.isub(s, m_add_one)
    });

    // (a+1)*1 = a+1
    let t6 = d.isub(sum5, add_a1);
    let p6_eq = d.const_app(p.mul_one, &[add_a1]);
    let p6 = d.icongr(m_add_one, add_a1, p6_eq, &|d, t| d.isub(sum5, t));

    // a+1 = 1+a
    let one_add_a = d.iadd(one_i, a);
    let t7 = d.isub(sum5, one_add_a);
    let p7_eq = d.const_app(p.add_comm, &[a, one_i]);
    let p7 = d.icongr(add_a1, one_add_a, p7_eq, &|d, t| d.isub(sum5, t));

    // (a*a+a) - (1+a) = a*a - 1
    let p8 = super::modeq::cancel_common_addend(d, aa, one_i, a);

    let (_, proof) = d.ichain(
        start,
        &[
            (t1, p1),
            (t2, p2),
            (t3, p3),
            (t4, p4),
            (t5, p5),
            (t6, p6),
            (t7, p7),
            (diff, p8),
        ],
    );
    proof
}

/// `Int.self_inverse_mod_prime :
/// ∀ p a,
///   (2 ≤ natAbs p ∧ ∀ d, d ∣ natAbs p → d = 1 ∨ d = natAbs p) →
///   0 < p → 1 ≤ a → a ≤ p - 1 →
///   ModEq p (a*a) one →
///   Or (ModEq p a one) (ModEq p a (p - one))`
///
/// The genuinely prime-theoretic content Wilson's theorem needs: an element
/// that is its own modular inverse is congruent to `1` or `-1` (here `p-1`).
/// `0 < p` is threaded explicitly rather than derived — every `ModEq`
/// congruence in this development needs it for the same reason
/// (`modeq.rs`'s header), and deriving it from `1 ≤ a ≤ p-1` alone would cost
/// more order arithmetic than the lemma's actual content.
///
/// Route: `a*a ≡ 1 [p]` gives `p ∣ (a*a - 1)` (`ModEq.symm` +
/// `modEq_iff_dvd`); `a*a - 1 = (a-1)(a+1)` ([`diff_of_squares`]) transports
/// that into `p ∣ (a-1)(a+1)`; `Int.euclid_lemma` — fed the *same* inline
/// primality clause it already uses — **constructively** decides which
/// factor `p` divides (Euclid's lemma, not excluded middle). Each branch
/// converts back to a `ModEq` via `modEq_iff_dvd`'s `mpr`: the `a-1` branch
/// directly; the `a+1` branch through `ModEq p (-1) a` (relying on the
/// kernel reducing `neg (neg one)` to `one` on the concrete literal, exactly
/// as `gcd.rs`'s own `neg_neg` helper does) and then a `ModEq p (-1) (p-1)`
/// bridge built from `Int.dvd_refl p` transported along
/// [`super::modeq::cancel_neg_add`]`(p, one)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_self_inverse_mod_prime(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.self_inverse_mod_prime, 2, &|d, v| {
        let (p_var, a) = (v[0], v[1]);
        let big_p = {
            let f = d.int().nat_abs;
            d.const_app(f, &[p_var])
        };
        let prime_ty = prime_condition(d, big_p);
        let zero = d.izero();
        let pos_ty = d.ilt(zero, p_var);
        let one_i = d.ione();
        let one_lb = d.ile(one_i, a);
        let p_minus_one = d.isub(p_var, one_i);
        let ub = d.ile(a, p_minus_one);
        let aa = d.imul(a, a);
        let sq_ty = super::modeq::imodeq(d, p_var, aa, one_i);
        let modeq_a_one = super::modeq::imodeq(d, p_var, a, one_i);
        let modeq_a_pm1 = super::modeq::imodeq(d, p_var, a, p_minus_one);
        let concl = d.or(modeq_a_one, modeq_a_pm1);

        let stmt = {
            let inner = d.arrow(sq_ty, concl);
            let with_ub = d.arrow(ub, inner);
            let with_lb = d.arrow(one_lb, with_ub);
            let with_pos = d.arrow(pos_ty, with_lb);
            d.arrow(prime_ty, with_pos)
        };

        let prime_fv = d.fresh_fvar();
        let h_prime = d.kernel().fvar(prime_fv);
        let pos_fv = d.fresh_fvar();
        let h_pos = d.kernel().fvar(pos_fv);
        let lb_fv = d.fresh_fvar();
        // Unused in the proof: primality + `0 < p` already force `p ≥ 2`, and
        // the algebra below never needs the concrete bound on `a` — kept
        // because the brief's statement carries it (`1 ≤ a ≤ p-1`), matching
        // the classical range Wilson's theorem quantifies `a` over.
        let _h_lb = d.kernel().fvar(lb_fv);
        let ub_fv = d.fresh_fvar();
        let _h_ub = d.kernel().fvar(ub_fv);
        let sq_fv = d.fresh_fvar();
        let h_sq = d.kernel().fvar(sq_fv);

        // Step 1: p ∣ (a*a - 1), from h_sq via ModEq.symm + modEq_iff_dvd.
        let symm_sq = d.const_app(p.mod_eq_symm, &[p_var, aa, one_i, h_sq]);
        let diff = d.isub(aa, one_i);
        let dvd_diff_ty = super::dvd::idvd(d, p_var, diff);
        let modeq_one_aa = super::modeq::imodeq(d, p_var, one_i, aa);
        let iff1 = d.const_app(p.mod_eq_iff_dvd, &[p_var, one_i, aa, h_pos]);
        let mp1 = d.const_app(p.logic.iff_mp, &[modeq_one_aa, dvd_diff_ty, iff1]);
        let dvd_diff = d.apply(mp1, &[symm_sq]);

        // Step 2: a*a - 1 = (a-1)*(a+1), transported.
        let sub_a1 = d.isub(a, one_i);
        let add_a1 = d.iadd(a, one_i);
        let prod = d.imul(sub_a1, add_a1);
        let prod_eq_start = diff_of_squares(d, a); // Eq Int prod diff
        let prod_eq = d.isymm(prod, diff, prod_eq_start); // Eq Int diff prod
        let motive = d.ieq_motive(diff, &|d, x| super::dvd::idvd(d, p_var, x));
        let dvd_prod = d.itransport(diff, motive, dvd_diff, prod, prod_eq);

        // Step 3: Euclid's lemma decides which factor `p` divides.
        let disj = d.const_app(p.euclid_lemma, &[p_var, sub_a1, add_a1, h_prime, dvd_prod]);
        let left_ty = super::dvd::idvd(d, p_var, sub_a1);
        let right_ty = super::dvd::idvd(d, p_var, add_a1);

        let on_left = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
            let modeq_one_a_ty = super::modeq::imodeq(d, p_var, one_i, a);
            let dvd_l_ty = super::dvd::idvd(d, p_var, sub_a1);
            let iff_l = d.const_app(p.mod_eq_iff_dvd, &[p_var, one_i, a, h_pos]);
            let mpr_l = d.const_app(p.logic.iff_mpr, &[modeq_one_a_ty, dvd_l_ty, iff_l]);
            let modeq_one_a = d.apply(mpr_l, &[h]);
            let modeq_a_one_pf = d.const_app(p.mod_eq_symm, &[p_var, one_i, a, modeq_one_a]);
            d.or_inl(modeq_a_one, modeq_a_pm1, modeq_a_one_pf)
        };

        let on_right = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
            let neg_one = d.ineg(one_i);

            // ModEq p (-1) a, from h : p ∣ (a+1), via `neg (neg one) = one`.
            let modeq_negone_a_ty = super::modeq::imodeq(d, p_var, neg_one, a);
            let a_minus_negone = d.isub(a, neg_one);
            let dvd_r1_ty = super::dvd::idvd(d, p_var, a_minus_negone);
            let iff_r1 = d.const_app(p.mod_eq_iff_dvd, &[p_var, neg_one, a, h_pos]);
            let mpr_r1 = d.const_app(p.logic.iff_mpr, &[modeq_negone_a_ty, dvd_r1_ty, iff_r1]);
            let modeq_negone_a = d.apply(mpr_r1, &[h]);
            let modeq_a_negone = d.const_app(p.mod_eq_symm, &[p_var, neg_one, a, modeq_negone_a]);

            // ModEq p (-1) (p-1), from `Int.dvd_refl p` transported along
            // `cancel_neg_add p one : (p + (-1)) + 1 = p`.
            let dvd_refl_p = d.const_app(p.dvd_refl, &[p_var]);
            let cna = super::modeq::cancel_neg_add(d, p_var, one_i);
            let cna_lhs = {
                let inner = d.iadd(p_var, neg_one);
                d.iadd(inner, one_i)
            };
            let reversed = d.isymm(cna_lhs, p_var, cna);
            let motive2 = d.ieq_motive(p_var, &|d, x| super::dvd::idvd(d, p_var, x));
            let result_r2 = d.itransport(p_var, motive2, dvd_refl_p, cna_lhs, reversed);

            let modeq_negone_pm1_ty = super::modeq::imodeq(d, p_var, neg_one, p_minus_one);
            let pm1_minus_negone = d.isub(p_minus_one, neg_one);
            let dvd_r2_ty = super::dvd::idvd(d, p_var, pm1_minus_negone);
            let iff_r2 = d.const_app(p.mod_eq_iff_dvd, &[p_var, neg_one, p_minus_one, h_pos]);
            let mpr_r2 = d.const_app(p.logic.iff_mpr, &[modeq_negone_pm1_ty, dvd_r2_ty, iff_r2]);
            let modeq_negone_pm1 = d.apply(mpr_r2, &[result_r2]);

            let modeq_a_pm1_pf = d.const_app(
                p.mod_eq_trans,
                &[
                    p_var,
                    a,
                    neg_one,
                    p_minus_one,
                    modeq_a_negone,
                    modeq_negone_pm1,
                ],
            );
            d.or_inr(modeq_a_one, modeq_a_pm1, modeq_a_pm1_pf)
        };

        let proof_body = d.or_elim(left_ty, right_ty, concl, disj, on_left, on_right);

        let with_sq = d.lam_fv(sq_fv, sq_ty, proof_body);
        let with_ub = d.lam_fv(ub_fv, ub, with_sq);
        let with_lb = d.lam_fv(lb_fv, one_lb, with_ub);
        let with_pos = d.lam_fv(pos_fv, pos_ty, with_lb);
        let proof = d.lam_fv(prime_fv, prime_ty, with_pos);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.factorial_pos : ∀ (n : Nat), 0 < factorial n`.
///
/// Induction on `n`: the base case is `0 < factorial zero`, defeq to
/// `zero_lt_one` (`factorial_zero` is `Eq.refl`); the step needs
/// `0 < ofNat (succ j)`, built from `Int.lt_of_nat_add zero j : 0 < 0 +
/// ofNat (succ j)` transported past `add_comm`/`add_zero`, then
/// `Int.mul_pos` closes `0 < factorial j * ofNat (succ j)`, defeq to
/// `0 < factorial (succ j)` (`factorial_succ` is `Eq.refl` too).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_factorial_pos(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let zero_i = d.izero();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let motive = |d: &mut IntDev<'_>, x: ExprId| {
        let f = d.const_app(p.factorial, &[x]);
        d.ilt(zero_i, f)
    };
    let stmt = motive(d, n);

    let proof_body = d.induct(
        &motive,
        &|d| d.const_app(p.zero_lt_one, &[]),
        &|d, j, ih| {
            let sj = d.succ(j);
            let sj_i = d.of_nat(sj);
            let base_lt = d.const_app(p.lt_of_nat_add, &[zero_i, j]); // 0 < 0 + sj_i
            let sum = d.iadd(zero_i, sj_i);
            let sj0 = d.iadd(sj_i, zero_i);
            let comm = d.const_app(p.add_comm, &[zero_i, sj_i]);
            let addz = d.const_app(p.add_zero, &[sj_i]);
            let (_, sum_eq_sji) = d.ichain(sum, &[(sj0, comm), (sj_i, addz)]);
            let motive2 = d.ieq_motive(sum, &|d, x| d.ilt(zero_i, x));
            let pos_sj = d.itransport(sum, motive2, base_lt, sj_i, sum_eq_sji);
            let factorial_j = d.const_app(p.factorial, &[j]);
            d.const_app(p.mul_pos, &[factorial_j, sj_i, ih, pos_sj])
        },
        n,
    );

    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, proof_body);
    d.declare_theorem(p.factorial_pos, ty, value)
}

// ============================================================================
// The coprime form of Fermat's little theorem, and the executable-inverse
// bridge it unlocks. `p ∤ a ⟹ a^(p−1) ≡ 1 [p]` — every ingredient below it
// (`Nat.pow_prime_modeq_self`, `Nat.coprime_of_lt_prime`,
// `Int.modEq_of_nat_modEq`, `Int.modEq_cancel`) landed the same day; this is
// the assembly.
// ============================================================================

/// `2 ≤ magnitude`, `∀ x, x ∣ magnitude → x = 1 ∨ x = magnitude` — the two
/// conjuncts [`prime_condition`] ANDs together, split out so `and_left` can
/// project `2 ≤ magnitude` back out of a primality proof. A deliberate
/// duplicate of `prime_condition`'s own construction (not a refactor of it):
/// identical builder calls in identical order intern to the identical
/// `ExprId`, so `and_left(two_le, clause, prime_proof)` type-checks against a
/// `prime_proof` built via [`prime_condition`] without either function
/// depending on the other's internals.
fn prime_parts(d: &mut IntDev<'_>, magnitude: ExprId) -> (ExprId, ExprId) {
    let nat = d.nat_ty();
    let two_nat = d.num(2);
    let one_nat = d.num(1);
    let two_le = d.le(two_nat, magnitude);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hyp = d.dvd(x, magnitude);
    let is_one = d.eq(x, one_nat);
    let is_whole = d.eq(x, magnitude);
    let disjunction = d.or(is_one, is_whole);
    let inner = d.arrow(hyp, disjunction);
    let clause = d.pi_fv(x_fv, nat, inner);
    (two_le, clause)
}

/// `prime magnitude → Nat.le 1 magnitude` — usable directly (via defeq,
/// `Nat.lt` unfolding to a `succ`-shifted `Nat.le`) wherever `0 < magnitude`
/// is wanted too. Mirrors `nat_prelude/fermat.rs`'s private `prime_pos`
/// exactly (that copy is not reachable from `int_prelude`), extracting
/// `2 ≤ magnitude` via `and_left` and weakening `1 ≤ 2 ≤ magnitude`.
fn nat_prime_pos(d: &mut IntDev<'_>, magnitude: ExprId, prime_proof: ExprId) -> ExprId {
    let p = d.int();
    let (two_le_ty, clause_ty) = prime_parts(d, magnitude);
    let two_le = d.and_left(two_le_ty, clause_ty, prime_proof);
    let one = d.num(1);
    let two = d.num(2);
    let one_le_two = d.lemma(p.nat.le_succ, &[one]);
    d.lemma(p.nat.le_trans, &[one, two, magnitude, one_le_two, two_le])
}

/// `(ofNat (pow base exp), pow (ofNat base) exp)` — the two sides
/// [`declare_of_nat_pow`]'s statement (and induction step) equates.
fn of_nat_pow_sides(d: &mut IntDev<'_>, base: ExprId, exp: ExprId) -> (ExprId, ExprId) {
    let pow_nat = d.pow(base, exp);
    let lhs = d.of_nat(pow_nat);
    let of_base = d.of_nat(base);
    let rhs = d.ipow(of_base, exp);
    (lhs, rhs)
}

/// `Int.of_nat_pow : ∀ (a n : Nat), Eq Int (ofNat (pow a n)) (pow (ofNat a) n)`.
///
/// `Int.ofNat` is a ring homomorphism on `+`/`*` at even a *symbolic* pair of
/// naturals — `Int.add`/`Int.mul` pattern-match on the outer `ofNat`/`negSucc`
/// constructor of their `Int` arguments, which is already determined for
/// `ofNat _` regardless of what is nested inside, so the `ofNat`-branch
/// reduction is `Eq.refl`-transparent even for free variables (the same fact
/// [`declare_modeq_of_nat_modeq`](super::modeq::declare_modeq_of_nat_modeq)'s
/// doc comment relies on). `Int.pow` does not get this for free: its
/// recursion is on the *exponent*, via `Nat.rec`, and a free-variable exponent
/// is not a constructor application, so no amount of unfolding reaches a
/// normal form. Hence this needs a genuine induction on `n`, not a `refl`.
///
/// Base (`n = zero`): both sides reduce, independently, to `ofNat 1`
/// (`Nat.pow_zero` then `Int.one := ofNat 1`; `Int.pow_zero` directly) — an
/// `Eq.refl`-shaped closure, same pattern as `factorial_zero`.
///
/// Step (`n = succ j`, `ih : Eq Int (ofNat (pow a j)) (pow (ofNat a) j)`):
/// `icongr ih (fun x => mul x (ofNat a))` gives `Eq Int (mul (ofNat (pow a j))
/// (ofNat a)) (mul (pow (ofNat a) j) (ofNat a))`; its left side is defeq to
/// `ofNat (pow a (succ j))` (`Nat.pow_succ`, then the same ofNat-branch
/// reduction as the base case) and its right side is defeq to `pow (ofNat a)
/// (succ j)` (`Int.pow_succ`) — so the `icongr` term, unadjusted, already has
/// the goal's type up to defeq.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_of_nat_pow(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.of_nat_pow, 2, &|d, v| {
        let (a, n) = (v[0], v[1]);
        let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let (lhs, rhs) = of_nat_pow_sides(d, a, x);
            d.ieq(lhs, rhs)
        };
        let stmt = motive(d, n);

        let proof = d.induct(
            &motive,
            &|d| {
                let one_i = d.ione();
                d.irefl(one_i)
            },
            &|d, j, ih| {
                let (lhs_j, rhs_j) = of_nat_pow_sides(d, a, j);
                let of_a = d.of_nat(a);
                d.icongr(lhs_j, rhs_j, ih, &|d, x| d.imul(x, of_a))
            },
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.pow_prime_sub_one_modeq_one :
/// ∀ p a, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) → 0 < a → a < p →
///   ModEq (ofNat p) (pow (ofNat a) (p-1)) one`
///
/// The coprime form of Fermat's little theorem: `p ∤ a ⟹ a^(p−1) ≡ 1 [p]`.
/// Kept over `ℤ` (not `ℕ`) because the one step this needs that `ℕ` cannot
/// supply is cancellation — `Int.modEq_cancel` — and the transport is
/// `ℕ → ℤ` only ([`super::modeq::declare_modeq_of_nat_modeq`]'s doc), so
/// carrying primality and the two range hypotheses in `ℕ` (matching
/// `Nat.pow_prime_modeq_self`/`Nat.coprime_of_lt_prime` exactly, no
/// `natAbs` detour) and casting only the *derived* congruence is the cheaper
/// split: it needed one bridging lemma ([`declare_of_nat_pow`]) instead of
/// redoing primality/order over `ℤ`.
///
/// Route:
/// 1. `Nat.pow_prime_modeq_self` gives `ModEq p (pow a p) a` over `ℕ`.
/// 2. `Nat.sub_add_cancel 1 p (1 ≤ p)` gives `Eq Nat (add (p-1) 1) p`, defeq
///    `Eq Nat (succ (p-1)) p` (`add x 1` reduces to `succ x` by the same
///    `add_succ`/`add_zero` `Eq.refl` pair `Nat.add`'s own equations use).
///    `Nat.pow_succ` at `p-1` gives `pow a (succ (p-1)) = pow a (p-1) * a`;
///    composing rewrites `pow a p` (step 1's exponent) into `pow a (p-1) * a`,
///    entirely over `ℕ`.
/// 3. `Int.modEq_of_nat_modEq` casts the rewritten congruence,
///    `ModEq p (pow a (p-1) * a) a`, to `ℤ` — landing (via the ofNat-branch
///    defeq [`declare_of_nat_pow`]'s doc comment describes) at
///    `ModEq (ofNat p) (mul (ofNat (pow a (p-1))) (ofNat a)) (ofNat a)`.
/// 4. [`declare_of_nat_pow`] reshapes `ofNat (pow a (p-1))` into
///    `pow (ofNat a) (p-1)` inside that congruence.
/// 5. `Int.mul_comm`/`Int.mul_one` reshape the congruence into
///    `ModEq (ofNat p) (mul (ofNat a) (pow (ofNat a) (p-1))) (mul (ofNat a) one)`
///    — the `c*x ≡ c*y` shape `Int.modEq_cancel` needs, `c := ofNat a`.
/// 6. `Nat.coprime_of_lt_prime` gives `Eq Nat (gcd a p) 1`, defeq to
///    `Coprime (ofNat a) (ofNat p)` (`Int.gcd`/`Int.natAbs` both reduce
///    transparently on an `ofNat` argument, symbolic or not). `Int.modEq_cancel`
///    then cancels the factor of `a`, landing exactly on the goal.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_pow_prime_sub_one_modeq_one(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.pow_prime_sub_one_modeq_one, 2, &|d, v| {
        let (pp, aa) = (v[0], v[1]);
        let prime_ty = prime_condition(d, pp);
        let zero = d.zero();
        let pos_ty = d.lt(zero, aa);
        let ub_ty = d.lt(aa, pp);

        let one_nat = d.num(1);
        let pm1 = d.sub(pp, one_nat);
        let big_p = d.of_nat(pp);
        let big_a = d.of_nat(aa);
        let pow_int = d.ipow(big_a, pm1);
        let one_i = d.ione();
        let concl = super::modeq::imodeq(d, big_p, pow_int, one_i);

        let stmt = {
            let inner = d.arrow(ub_ty, concl);
            let with_pos = d.arrow(pos_ty, inner);
            d.arrow(prime_ty, with_pos)
        };

        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);
        let pos_fv = d.fresh_fvar();
        let pos_proof = d.kernel().fvar(pos_fv);
        let ub_fv = d.fresh_fvar();
        let ub_proof = d.kernel().fvar(ub_fv);

        // Step 0: 1 ≤ p (also usable as 0 < p, `Nat.lt` unfolding to a
        // succ-shifted `Nat.le`).
        let one_le_pp = nat_prime_pos(d, pp, prime_proof);

        // Step 2: succ(p-1) = p.
        let cancel = d.lemma(p.nat.sub_add_cancel, &[one_nat, pp, one_le_pp]);
        let succ_pm1 = d.succ(pm1);

        // Step 1: Nat.ModEq p (pow a p) a.
        let nat_fermat_fn = d.lemma(p.nat.pow_prime_modeq_self, &[pp, aa]);
        let nat_fermat = d.apply(nat_fermat_fn, &[prime_proof]);

        // Step 2 (continued): pow a p = pow a (p-1) * a, over Nat.
        let pow_aa_pp = d.pow(aa, pp);
        let pow_aa_succpm1 = d.pow(aa, succ_pm1);
        let pow_aa_pm1 = d.pow(aa, pm1);
        let mul_term = d.mul(pow_aa_pm1, aa);
        let pow_succ_pm1 = d.lemma(p.nat.pow_succ, &[aa, pm1]);
        let congr_exp = d.congr(succ_pm1, pp, cancel, &|d, x| d.pow(aa, x));
        let rev_congr_exp = d.symm(pow_aa_succpm1, pow_aa_pp, congr_exp);
        let pow_pp_eq = d.trans(
            pow_aa_pp,
            pow_aa_succpm1,
            mul_term,
            rev_congr_exp,
            pow_succ_pm1,
        );

        let motive_nat = d.eq_motive(pow_aa_pp, &|d, x| d.mod_eq(pp, x, aa));
        let nat_rewritten = d.transport(pow_aa_pp, motive_nat, nat_fermat, mul_term, pow_pp_eq);

        // Step 3: cast to Int.
        let int_pre = d.const_app(p.mod_eq_of_nat_mod_eq, &[pp, mul_term, aa]);
        let int_form = d.apply(int_pre, &[nat_rewritten, one_le_pp]);

        // Step 4: reshape ofNat(pow a (p-1)) into pow (ofNat a) (p-1).
        let of_nat_powpm1 = d.of_nat(pow_aa_pm1);
        let bridge = d.const_app(p.of_nat_pow, &[aa, pm1]);
        let step4 = d.int_eq_rewrite(of_nat_powpm1, pow_int, bridge, int_form, &|d, x| {
            let mulx = d.imul(x, big_a);
            super::modeq::imodeq(d, big_p, mulx, big_a)
        });

        // Step 5: commute, then turn the trailing `a` into `a*1`.
        let mul_comm_pf = d.const_app(p.mul_comm, &[pow_int, big_a]);
        let lhs5 = d.imul(pow_int, big_a);
        let rhs5 = d.imul(big_a, pow_int);
        let step5a = d.int_eq_rewrite(lhs5, rhs5, mul_comm_pf, step4, &|d, x| {
            super::modeq::imodeq(d, big_p, x, big_a)
        });

        let mul_one_pf = d.const_app(p.mul_one, &[big_a]);
        let a_times_one = d.imul(big_a, one_i);
        let rev_mul_one = d.isymm(a_times_one, big_a, mul_one_pf);
        let step5b = d.int_eq_rewrite(big_a, a_times_one, rev_mul_one, step5a, &|d, x| {
            let lhs = d.imul(big_a, pow_int);
            super::modeq::imodeq(d, big_p, lhs, x)
        });

        // Step 6: coprimality, then cancel.
        let coprime_fn = d.lemma(p.nat.coprime_of_lt_prime, &[pp, aa]);
        let coprime_proof = d.apply(coprime_fn, &[prime_proof, pos_proof, ub_proof]);

        let cancel_fn = d.const_app(p.mod_eq_cancel, &[big_p, big_a, pow_int, one_i]);
        let final_proof = d.apply(cancel_fn, &[one_le_pp, coprime_proof, step5b]);

        let with_ub = d.lam_fv(ub_fv, ub_ty, final_proof);
        let with_pos = d.lam_fv(pos_fv, pos_ty, with_ub);
        let proof = d.lam_fv(prime_fv, prime_ty, with_pos);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// The executable inverse: `Int.mul_inv_of_pow` (one more split of Fermat) and
// `Nat.inverseIndex` (the closed-form `Nat → Nat` map), the pieces
// `Int.prodRange_permute` needs a concrete `σ` from.
// ============================================================================

/// `Int.mul_inv_of_pow :
/// ∀ p a, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) → 0 < a → a < p →
///   ModEq (ofNat p) (mul (ofNat a) (pow (ofNat a) (p-2))) one`
///
/// One more split of [`declare_pow_prime_sub_one_modeq_one`]:
/// `a^(p-1) = a^(p-2)*a`, so `a*a^(p-2) ≡ 1 [p]`. The closed form `a^(p-2)`
/// is what makes an *executable* inverse possible: `Int.modEq_inverse_exists`
/// only gives a `Prop`-level existential, which cannot eliminate into the
/// `Type`-valued function [`Nat.inverseIndex`] below — the same wall
/// `CReal.inv` and `pos_bound_of_lt` hit, and worth naming as a pattern: four
/// separate things in this development have needed a closed form for exactly
/// this reason.
///
/// Route: `succ(p-2) = p-1` from two `Nat.sub_add_cancel`s (at `2` and at
/// `1`) glued by `Nat.succ_injective` (both applied to the SAME prime `p`, so
/// they land on a common `p = succ _` shape without ever pattern-matching
/// `p` itself — `p` stays a free variable throughout, only the two `sub`
/// results are related). `Int.pow_succ` then splits `a^(p-1)` into
/// `a^(p-2)*a`, [`declare_pow_prime_sub_one_modeq_one`]'s congruence is
/// rewritten through that split, and `Int.mul_comm` moves the base `a` to
/// the front.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_mul_inv_of_pow(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.mul_inv_of_pow, 2, &|d, v| {
        let (pp, aa) = (v[0], v[1]);
        let prime_ty = prime_condition(d, pp);
        let zero = d.zero();
        let pos_ty = d.lt(zero, aa);
        let ub_ty = d.lt(aa, pp);

        let one_nat = d.num(1);
        let two_nat = d.num(2);
        let pm2 = d.sub(pp, two_nat);
        let big_p = d.of_nat(pp);
        let big_a = d.of_nat(aa);
        let pow_pm2 = d.ipow(big_a, pm2);
        let one_i = d.ione();
        let concl_lhs = d.imul(big_a, pow_pm2);
        let concl = super::modeq::imodeq(d, big_p, concl_lhs, one_i);

        let stmt = {
            let inner = d.arrow(ub_ty, concl);
            let with_pos = d.arrow(pos_ty, inner);
            d.arrow(prime_ty, with_pos)
        };

        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);
        let pos_fv = d.fresh_fvar();
        let pos_proof = d.kernel().fvar(pos_fv);
        let ub_fv = d.fresh_fvar();
        let ub_proof = d.kernel().fvar(ub_fv);

        // succ(p-2) = p-1, via two `sub_add_cancel`s glued by `succ_injective`.
        let (two_le_ty, clause_ty) = prime_parts(d, pp);
        let two_le = d.and_left(two_le_ty, clause_ty, prime_proof);
        let one_le_pp = nat_prime_pos(d, pp, prime_proof);

        let succ_pm2 = d.succ(pm2);
        let succ_succ_pm2 = d.succ(succ_pm2);
        let cancel2 = d.lemma(p.nat.sub_add_cancel, &[two_nat, pp, two_le]);
        let pm1 = d.sub(pp, one_nat);
        let succ_pm1 = d.succ(pm1);
        let cancel1 = d.lemma(p.nat.sub_add_cancel, &[one_nat, pp, one_le_pp]);
        let cancel1_rev = d.symm(succ_pm1, pp, cancel1);
        let combined = d.trans(succ_succ_pm2, pp, succ_pm1, cancel2, cancel1_rev);
        let succ_injective_fn = d.lemma(p.nat.succ_injective, &[succ_pm2, pm1]);
        let succ_pm2_eq_pm1 = d.apply(succ_injective_fn, &[combined]);

        // a^(p-1) = a^(p-2) * a, over Int.
        let pow_pm1 = d.ipow(big_a, pm1);
        let ipow_succ_pm2 = d.ipow(big_a, succ_pm2);
        let pow_succ_congr =
            d.nat_eq_to_int(succ_pm2, pm1, succ_pm2_eq_pm1, &|d, x| d.ipow(big_a, x));
        let pow_succ_pf = d.const_app(p.pow_succ, &[big_a, pm2]);
        let mul_term = d.imul(pow_pm2, big_a);
        let step_a = d.isymm(ipow_succ_pm2, pow_pm1, pow_succ_congr);
        let step1_eq = d.itrans(pow_pm1, ipow_succ_pm2, mul_term, step_a, pow_succ_pf);

        // The base Fermat congruence, rewritten through that split.
        let base_fermat = d.const_app(
            p.pow_prime_sub_one_modeq_one,
            &[pp, aa, prime_proof, pos_proof, ub_proof],
        );
        let rewritten = d.int_eq_rewrite(pow_pm1, mul_term, step1_eq, base_fermat, &|d, x| {
            super::modeq::imodeq(d, big_p, x, one_i)
        });

        // Commute to put the base first.
        let mul_comm_pf = d.const_app(p.mul_comm, &[pow_pm2, big_a]);
        let final_proof = d.int_eq_rewrite(mul_term, concl_lhs, mul_comm_pf, rewritten, &|d, x| {
            super::modeq::imodeq(d, big_p, x, one_i)
        });

        let with_ub = d.lam_fv(ub_fv, ub_ty, final_proof);
        let with_pos = d.lam_fv(pos_fv, pos_ty, with_ub);
        let proof = d.lam_fv(prime_fv, prime_ty, with_pos);
        (stmt, proof)
    })?;
    Ok(())
}

/// Delta height for `Nat.inverseIndex`, strictly above `Int.pow`'s own height
/// (it calls `Int.pow` via `Int.emod`'s argument, transitively through
/// `Int.ofNat`/`Int.emod`/`Int.natAbs`/`Nat.sub`).
const INVERSE_INDEX_HEIGHT: u16 = FACTORIAL_HEIGHT + 1;

/// Admit `Nat.inverseIndex : Nat → Nat → Nat :=
/// fun p k => natAbs (emod (pow (ofNat (succ k)) (p-2)) (ofNat p)) - 1`.
///
/// The settled indexing (this file's module doc): `a := ofNat(k+1)` for
/// `k < n` with `n := p - 1`, so `k` ranging over `{0,…,p-2}` puts `a` over
/// `{1,…,p-1}`. `a^(p-2) mod p` (`Int.emod`, always in `[0,p)`) is `a`'s
/// modular inverse's representative — [`declare_mul_inv_of_pow`] is exactly
/// `a * a^(p-2) ≡ 1 [p]` — and since that representative is itself in
/// `{1,…,p-1}` (never `0`: `a` is coprime to `p`, so `a^(p-2)` is too), the
/// closing `- 1` (truncated `Nat.sub`) puts the *result* back into
/// `{0,…,p-2}` — the same index range `k` came from, which is what
/// `[declare_inverse_index_maps_into]` and `[declare_inverse_index_injective]`
/// (both still open) need to state `MapsInto`/`InjectiveOn` at.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the generated definition does not
/// type-check or the name is already taken.
pub(super) fn declare_inverse_index(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();

    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let sk = d.succ(k);
    let base = d.of_nat(sk);
    let pm2 = d.sub(pp, two_nat);
    let pw = d.ipow(base, pm2);
    let big_p = d.of_nat(pp);
    let r = d.iemod(pw, big_p);
    let mag = {
        let f = p.nat_abs;
        d.const_app(f, &[r])
    };
    let body = d.sub(mag, one_nat);

    let value = {
        let with_k = d.lam_fv(k_fv, nat, body);
        d.lam_fv(pp_fv, nat, with_k)
    };
    let ty = {
        let with_k = d.arrow(nat, nat);
        d.arrow(nat, with_k)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.inverse_index,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(INVERSE_INDEX_HEIGHT),
    })
}

/// `pos : Lt zero_i x  ⊢  Not (Eq Int x zero_i)` — a positive integer is
/// nonzero: assume `x = 0`, rewrite `pos` along it to `Lt zero_i zero_i`,
/// refute with `Int.lt_irrefl`.
fn int_ne_zero_of_pos(d: &mut IntDev<'_>, x: ExprId, pos: ExprId) -> ExprId {
    let p = d.int();
    let zero_i = d.izero();
    let eq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(eq_fv);
    let rewritten = d.int_eq_rewrite(x, zero_i, heq, pos, &|d, y| {
        let z = d.izero();
        d.ilt(z, y)
    });
    let irrefl = d.const_app(p.lt_irrefl, &[zero_i]);
    let false_pf = d.apply(irrefl, &[rewritten]);
    let eq_ty = d.ieq(x, zero_i);
    d.lam_fv(eq_fv, eq_ty, false_pf)
}

/// `prime_proof : (prime condition on pp)  ⊢  Le one (sub pp one)`, i.e.
/// `0 < p - 1` (`Nat.lt` unfolds to a `succ`-shifted `Nat.le`, so this
/// doubles as `Lt zero (sub pp one)`).
///
/// From `2 ≤ p` (the first conjunct of primality) and `succ(p-1) = p`
/// (`Nat.sub_add_cancel` at `1`), transported and peeled by
/// `Nat.le_of_succ_le_succ`.
fn one_le_pred(d: &mut IntDev<'_>, pp: ExprId, pm1: ExprId, prime_proof: ExprId) -> ExprId {
    let p = d.int();
    let one_nat = d.num(1);
    let (two_le_ty, clause_ty) = prime_parts(d, pp);
    let two_le = d.and_left(two_le_ty, clause_ty, prime_proof);
    let one_le_pp = nat_prime_pos(d, pp, prime_proof);
    let succ_pm1 = d.succ(pm1);
    let cancel1 = d.lemma(p.nat.sub_add_cancel, &[one_nat, pp, one_le_pp]);
    let cancel1_rev = d.symm(succ_pm1, pp, cancel1);
    let transported = d.nat_rewrite(pp, succ_pm1, cancel1_rev, two_le, &|d, x| {
        let two = d.num(2);
        d.le(two, x)
    });
    let peel = d.lemma(p.nat.le_of_succ_le_succ, &[one_nat, pm1]);
    d.apply(peel, &[transported])
}

/// `Nat.inverseIndex_maps_into :
/// ∀ p, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) →
///   MapsInto (fun k => inverseIndex p k) (p-1)`
///
/// The inverse of a residue is a residue: `Int.emod` always lands in
/// `[0, ofNat p)` (`Int.emod_nonneg` / `Int.emod_lt_of_pos`, needing only
/// `ofNat p ≠ 0` / `0 < ofNat p`, both from primality — no need to touch
/// [`declare_mul_inv_of_pow`] or coprimality at all). `Int.lt` on two
/// `ofNat`-headed arguments reduces STRUCTURALLY to `Nat.lt`
/// (`int_prelude/defs.rs`'s four-case table for `Int.le`/`Int.lt`), so once
/// `r`'s `Int.emod` bound is rewritten from `r` to `ofNat (natAbs r)` (via
/// `Int.of_nat_nat_abs_of_nonneg`), the resulting `Lt (ofNat (natAbs r))
/// (ofNat p)` **is** `Nat.lt (natAbs r) p` up to defeq — no extra
/// order-transfer lemma needed. From there, `natAbs r ≤ p - 1`
/// (`Nat.le_of_lt_succ` after rewriting `p` to `succ (p-1)`).
///
/// The closing `- 1` (truncated `Nat.sub`) needs a case split on whether
/// `natAbs r` is `0`: if so, truncation floors the result at `0`, and
/// `0 < p - 1` (`one_le_pred`, primality again) closes it; otherwise
/// `Nat.sub_lt` gives the strict step directly and `Nat.lt_of_lt_of_le`
/// composes it with the bound above. Landing this needed **no** argument
/// that `natAbs r ≠ 0` (which would need coprimality) — `Nat.lt_or_eq_of_le`
/// covers both outcomes, the same truncation safety net this file's module
/// doc already flagged for `p = 2`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_inverse_index_maps_into(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    d.theorem(p.inverse_index_maps_into, 1, &|d, v| {
        let pp = v[0];
        let prime_ty = prime_condition(d, pp);

        let one_nat = d.num(1);
        let two_nat = d.num(2);
        let pm1 = d.sub(pp, one_nat);
        let sigma = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let body = d.const_app(p.inverse_index, &[pp, k]);
            d.lam_fv(k_fv, nat, body)
        };
        let concl = d.const_app(p.nat.maps_into, &[sigma, pm1]);
        let stmt = d.arrow(prime_ty, concl);

        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);

        let succ_pm1 = d.succ(pm1);
        let one_le_pp = nat_prime_pos(d, pp, prime_proof);
        let cancel1 = d.lemma(p.nat.sub_add_cancel, &[one_nat, pp, one_le_pp]);
        let cancel1_rev = d.symm(succ_pm1, pp, cancel1);
        let pm1_pos = one_le_pred(d, pp, pm1, prime_proof);

        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hyp_fv = d.fresh_fvar();
        let hyp_ty = d.lt(i, pm1);

        let sk_i = d.succ(i);
        let base_a = d.of_nat(sk_i);
        let big_p = d.of_nat(pp);
        let pos_big_p = one_le_pp;
        let ne_big_p = int_ne_zero_of_pos(d, big_p, pos_big_p);

        let pm2 = d.sub(pp, two_nat);
        let pw = d.ipow(base_a, pm2);
        let r = d.iemod(pw, big_p);
        let mag = {
            let f = p.nat_abs;
            d.const_app(f, &[r])
        };

        let r_nonneg = d.const_app(p.emod_nonneg, &[pw, big_p, ne_big_p]);
        let r_lt = d.const_app(p.emod_lt_of_pos, &[pw, big_p, pos_big_p]);
        let bridge = d.const_app(p.of_nat_nat_abs_of_nonneg, &[r, r_nonneg]);
        let ofnat_mag = d.of_nat(mag);
        let bridge_rev = d.isymm(ofnat_mag, r, bridge);
        let mag_lt_pp = d.int_eq_rewrite(r, ofnat_mag, bridge_rev, r_lt, &|d, x| d.ilt(x, big_p));

        let mag_lt_succ_pm1 =
            d.nat_rewrite(pp, succ_pm1, cancel1_rev, mag_lt_pp, &|d, x| d.lt(mag, x));
        let peel = d.lemma(p.nat.le_of_lt_succ, &[mag, pm1]);
        let mag_le_pm1 = d.apply(peel, &[mag_lt_succ_pm1]);

        let zero_nat = d.zero();
        let zero_le_mag = d.lemma(p.nat.zero_le, &[mag]);
        let case_pf = d.lemma(p.nat.lt_or_eq_of_le, &[zero_nat, mag, zero_le_mag]);

        let result_ty = {
            let sm = d.sub(mag, one_nat);
            d.lt(sm, pm1)
        };
        let mag_pos_ty = d.lt(zero_nat, mag);
        let mag_zero_ty = d.eq(zero_nat, mag);

        let on_pos = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
            let z = d.zero();
            let one_pos = d.lemma(p.nat.zero_lt_succ, &[z]);
            let sub_lt_pf = d.lemma(p.nat.sub_lt, &[mag, one_nat, h, one_pos]);
            let sm = d.sub(mag, one_nat);
            d.lemma(p.nat.lt_of_lt_of_le, &[sm, mag, pm1, sub_lt_pf, mag_le_pm1])
        };
        let on_zero = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
            d.nat_rewrite(zero_nat, mag, h, pm1_pos, &|d, x| {
                let s = d.sub(x, one_nat);
                d.lt(s, pm1)
            })
        };
        let result = d.or_elim(mag_pos_ty, mag_zero_ty, result_ty, case_pf, on_pos, on_zero);

        let inner_body = {
            let with_hyp = d.lam_fv(hyp_fv, hyp_ty, result);
            d.lam_fv(i_fv, nat, with_hyp)
        };
        let proof = d.lam_fv(prime_fv, prime_ty, inner_body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `0 < n → 0 ≤ x → x < n  ⊢  Eq Int (emod x n) x` — `Int.emod` is the
/// identity on an already-reduced nonnegative representative. `x` is a
/// `(q,r)`-decomposition of itself against `n` with `q := 0, r := x`
/// (bounds given), and `Int.ediv_add_emod` supplies the OTHER decomposition
/// `x = n*(x/n) + x%n` with `Int.emod_nonneg`/`Int.emod_lt_of_pos` bounding
/// its remainder; `Int.ediv_emod_unique` forces the two remainders equal.
fn emod_eq_self_of_in_range(
    d: &mut IntDev<'_>,
    x: ExprId,
    n: ExprId,
    n_pos: ExprId,
    x_nonneg: ExprId,
    x_lt: ExprId,
) -> ExprId {
    let p = d.int();
    let zero_i = d.izero();
    let ediv_xn = d.iediv(x, n);
    let emod_xn = d.iemod(x, n);

    // decomp1 : x = n*zero + x.
    let n_zero = d.imul(n, zero_i);
    let mul_zero_pf = d.const_app(p.mul_zero, &[n]);
    let sum1 = d.iadd(n_zero, x);
    let sum1b = d.iadd(zero_i, x);
    let zero_add_pf = d.icongr(n_zero, zero_i, mul_zero_pf, &|d, t| d.iadd(t, x));
    let add_comm_pf = d.const_app(p.add_comm, &[zero_i, x]);
    let x_zero = d.iadd(x, zero_i);
    let add_zero_pf = d.const_app(p.add_zero, &[x]);
    let (_, sum1_eq_x) = d.ichain(
        sum1,
        &[
            (sum1b, zero_add_pf),
            (x_zero, add_comm_pf),
            (x, add_zero_pf),
        ],
    );
    let decomp1 = d.isymm(sum1, x, sum1_eq_x);

    // decomp2 : x = n*(x/n) + x%n.
    let n_ediv = d.imul(n, ediv_xn);
    let sum2 = d.iadd(n_ediv, emod_xn);
    let ediv_add_emod_pf = d.const_app(p.ediv_add_emod, &[x, n]);
    let decomp2 = d.isymm(sum2, x, ediv_add_emod_pf);

    let ne_n = int_ne_zero_of_pos(d, n, n_pos);
    let r2_nonneg = d.const_app(p.emod_nonneg, &[x, n, ne_n]);
    let r2_lt = d.const_app(p.emod_lt_of_pos, &[x, n, n_pos]);

    let uniq = d.const_app(
        p.ediv_emod_unique,
        &[
            x, n, zero_i, x, ediv_xn, emod_xn, n_pos, decomp1, x_nonneg, x_lt, decomp2, r2_nonneg,
            r2_lt,
        ],
    );
    let q_ty = d.ieq(zero_i, ediv_xn);
    let r_ty = d.ieq(x, emod_xn);
    let r_eq = d.and_right(q_ty, r_ty, uniq);
    d.isymm(x, emod_xn, r_eq)
}

/// `hne : Le zero n  ⊢  Lt zero n`, given `hne : Not (Eq Nat n zero)` — a
/// nonzero natural is positive. `Nat.zero_le` always gives `0 ≤ n`;
/// `Nat.lt_or_eq_of_le` splits that into the wanted `0 < n` or `0 = n`, and
/// the second branch contradicts `hne` directly.
fn pos_of_ne_zero(d: &mut IntDev<'_>, n: ExprId, hne: ExprId) -> ExprId {
    let p = d.int();
    let zero_nat = d.zero();
    let zero_le_n = d.lemma(p.nat.zero_le, &[n]);
    let case_pf = d.lemma(p.nat.lt_or_eq_of_le, &[zero_nat, n, zero_le_n]);
    let pos_ty = d.lt(zero_nat, n);
    let eq_ty = d.eq(zero_nat, n);
    let on_pos = &|_d: &mut IntDev<'_>, h: ExprId| -> ExprId { h };
    let on_eq = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
        let h_rev = d.symm(zero_nat, n, h);
        let false_pf = d.apply(hne, &[h_rev]);
        let target = d.lt(zero_nat, n);
        d.absurd(target, false_pf)
    };
    d.or_elim(pos_ty, eq_ty, pos_ty, case_pf, on_pos, on_eq)
}

/// `prime_proof, 0 < sx, sx < pp  ⊢  Not (Eq Nat mag zero)`, where
/// `mag := natAbs (emod (pow (ofNat sx) (pp-2)) (ofNat pp))` — the modular
/// inverse of a residue coprime to `p` is never `0`.
///
/// If it were, [`declare_mul_inv_of_pow`] plus `Int.mod_eq_mul_left` and
/// `Int.mul_zero` would give `ModEq p 1 0`; `Int.emod` is the identity on
/// both canonical representatives `0` and `1`
/// ([`emod_eq_self_of_in_range`]), so that forces `Eq Int 1 0` — refuted by
/// `Nat.succ_ne_zero` after an `Int.natAbs` congruence turns it into
/// `Eq Nat 1 0`.
fn mag_ne_zero(
    d: &mut IntDev<'_>,
    pp: ExprId,
    sx: ExprId,
    prime_proof: ExprId,
    pos_sx: ExprId,
    ub_sx: ExprId,
) -> ExprId {
    let p = d.int();
    let two_nat = d.num(2);
    let one_nat = d.num(1);
    let zero_nat = d.zero();
    let zero_i = d.izero();
    let one_i = d.ione();

    let one_le_pp = nat_prime_pos(d, pp, prime_proof);
    let pos_big_p = one_le_pp;
    let (two_le_ty, clause_ty) = prime_parts(d, pp);
    let two_le = d.and_left(two_le_ty, clause_ty, prime_proof);

    let big_p = d.of_nat(pp);
    let ax = d.of_nat(sx);
    let pm2 = d.sub(pp, two_nat);
    let pw_x = d.ipow(ax, pm2);
    let r_x = d.iemod(pw_x, big_p);
    let mag_x = {
        let f = p.nat_abs;
        d.const_app(f, &[r_x])
    };

    let mag_fv = d.fresh_fvar();
    let h0 = d.kernel().fvar(mag_fv);

    let ne_big_p = int_ne_zero_of_pos(d, big_p, pos_big_p);
    let r_nonneg = d.const_app(p.emod_nonneg, &[pw_x, big_p, ne_big_p]);
    let bridge = d.const_app(p.of_nat_nat_abs_of_nonneg, &[r_x, r_nonneg]);
    let congr0 = d.nat_eq_to_int(mag_x, zero_nat, h0, &|d, y| d.of_nat(y));
    let ofnat_mag = d.of_nat(mag_x);
    let bridge_rev = d.isymm(ofnat_mag, r_x, bridge);
    let r_eq_zero = d.itrans(r_x, ofnat_mag, zero_i, bridge_rev, congr0);

    let le_refl_zero = d.const_app(p.le_refl, &[zero_i]);
    let emod_zero_eq =
        emod_eq_self_of_in_range(d, zero_i, big_p, pos_big_p, le_refl_zero, pos_big_p);
    let zero_lt_one = d.const_app(p.zero_lt_one, &[]);
    let one_nonneg = d.const_app(p.le_of_lt, &[zero_i, one_i, zero_lt_one]);
    let emod_one_eq = emod_eq_self_of_in_range(d, one_i, big_p, pos_big_p, one_nonneg, two_le);

    let emod_pwx = d.iemod(pw_x, big_p);
    let emod_zero_raw = d.iemod(zero_i, big_p);
    let emod_zero_raw_rev = d.isymm(emod_zero_raw, zero_i, emod_zero_eq);
    let modeq_pw_zero = d.itrans(
        emod_pwx,
        zero_i,
        emod_zero_raw,
        r_eq_zero,
        emod_zero_raw_rev,
    );

    let mip_x = d.const_app(p.mul_inv_of_pow, &[pp, sx, prime_proof, pos_sx, ub_sx]);
    let cong = d.const_app(
        p.mod_eq_mul_left,
        &[big_p, pw_x, zero_i, ax, pos_big_p, modeq_pw_zero],
    );
    let mul_zero_ax = d.const_app(p.mul_zero, &[ax]);
    let ax_pwx = d.imul(ax, pw_x);
    let ax_zero = d.imul(ax, zero_i);
    let cong_rewritten = d.int_eq_rewrite(ax_zero, zero_i, mul_zero_ax, cong, &|d, y| {
        super::modeq::imodeq(d, big_p, ax_pwx, y)
    });
    let mip_symm = d.const_app(p.mod_eq_symm, &[big_p, ax_pwx, one_i, mip_x]);
    let modeq_one_zero = d.const_app(
        p.mod_eq_trans,
        &[big_p, one_i, ax_pwx, zero_i, mip_symm, cong_rewritten],
    );

    let emod_one_p = d.iemod(one_i, big_p);
    let emod_zero_p = d.iemod(zero_i, big_p);
    let emod_one_p_rev = d.isymm(emod_one_p, one_i, emod_one_eq);
    let (_, one_eq_zero) = d.ichain(
        one_i,
        &[
            (emod_one_p, emod_one_p_rev),
            (emod_zero_p, modeq_one_zero),
            (zero_i, emod_zero_eq),
        ],
    );

    let refl_one = d.refl(one_nat);
    let nat_eq = d.int_eq_rewrite(one_i, zero_i, one_eq_zero, refl_one, &|d, x| {
        let nx = {
            let f = p.nat_abs;
            d.const_app(f, &[x])
        };
        d.eq(one_nat, nx)
    });
    let sne = d.lemma(p.nat.succ_ne_zero, &[zero_nat]);
    let false_pf = d.apply(sne, &[nat_eq]);

    let eq_ty = d.eq(mag_x, zero_nat);
    d.lam_fv(mag_fv, eq_ty, false_pf)
}

/// `Nat.inverseIndex_injective :
/// ∀ p, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) →
///   InjectiveOn (fun k => inverseIndex p k) (p-1)`
///
/// If two indices have the same inverse, their inverses' inverses coincide:
/// `mag_ne_zero` (both indices) plus `Nat.sub_add_cancel` cancels the
/// closing `- 1` in `inverseIndex`'s definition, giving `mag i = mag j`
/// (Nat), hence `r i = r j` (Int, via `Int.of_nat_nat_abs_of_nonneg`), hence
/// `ModEq p (a_i^(p-2)) (a_j^(p-2))` (definitionally — `r` **is** that
/// `emod`). [`declare_mul_inv_of_pow`] commuted plus `Int.modEq_mul_right`/
/// `Int.modEq_trans` turns that into two congruences `ModEq p (a_i^(p-2) *
/// a_i) one` / `ModEq p (a_i^(p-2) * a_j) one`, and `Int.modEq_inverse_unique`
/// collapses them to `ModEq p a_i a_j`. `Int.emod` is the identity on both
/// (`emod_eq_self_of_in_range`, bounds from the same `Int.lt`-on-`ofNat`
/// structural reduction [`declare_inverse_index_maps_into`] uses), so that
/// forces `Eq Int a_i a_j`, and `Int.natAbs` congruence plus
/// `Nat.succ_injective` closes `Eq Nat i j`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_inverse_index_injective(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    d.theorem(p.inverse_index_injective, 1, &|d, v| {
        let pp = v[0];
        let prime_ty = prime_condition(d, pp);

        let one_nat = d.num(1);
        let two_nat = d.num(2);
        let pm1 = d.sub(pp, one_nat);
        let sigma = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let body = d.const_app(p.inverse_index, &[pp, k]);
            d.lam_fv(k_fv, nat, body)
        };
        let concl = d.const_app(p.nat.injective_on, &[sigma, pm1]);
        let stmt = d.arrow(prime_ty, concl);

        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);

        let succ_pm1 = d.succ(pm1);
        let one_le_pp = nat_prime_pos(d, pp, prime_proof);
        let pos_big_p = one_le_pp;
        let cancel1 = d.lemma(p.nat.sub_add_cancel, &[one_nat, pp, one_le_pp]);
        let big_p = d.of_nat(pp);
        let ne_big_p = int_ne_zero_of_pos(d, big_p, pos_big_p);
        let one_i = d.ione();

        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hi_ty = d.lt(i, pm1);
        let hj_fv = d.fresh_fvar();
        let hj = d.kernel().fvar(hj_fv);
        let hj_ty = d.lt(j, pm1);

        let sk_i = d.succ(i);
        let sk_j = d.succ(j);
        let a_i = d.of_nat(sk_i);
        let a_j = d.of_nat(sk_j);
        let pm2 = d.sub(pp, two_nat);
        let pw_i = d.ipow(a_i, pm2);
        let pw_j = d.ipow(a_j, pm2);
        let r_i = d.iemod(pw_i, big_p);
        let r_j = d.iemod(pw_j, big_p);
        let mag_i = {
            let f = p.nat_abs;
            d.const_app(f, &[r_i])
        };
        let mag_j = {
            let f = p.nat_abs;
            d.const_app(f, &[r_j])
        };

        let heq_ty = {
            let sm_i = d.sub(mag_i, one_nat);
            let sm_j = d.sub(mag_j, one_nat);
            d.eq(sm_i, sm_j)
        };
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        // succ i < pp, succ j < pp — from `i < pm1`/`j < pm1` and `succ pm1 = pp`.
        let mono_i_fn = d.lemma(p.nat.succ_le_succ, &[sk_i, pm1]);
        let mono_i = d.apply(mono_i_fn, &[hi]);
        let ub_i = d.nat_rewrite(succ_pm1, pp, cancel1, mono_i, &|d, x| {
            let s = d.succ(sk_i);
            d.le(s, x)
        });
        let mono_j_fn = d.lemma(p.nat.succ_le_succ, &[sk_j, pm1]);
        let mono_j = d.apply(mono_j_fn, &[hj]);
        let ub_j = d.nat_rewrite(succ_pm1, pp, cancel1, mono_j, &|d, x| {
            let s = d.succ(sk_j);
            d.le(s, x)
        });
        let pos_i = d.lemma(p.nat.zero_lt_succ, &[i]);
        let pos_j = d.lemma(p.nat.zero_lt_succ, &[j]);

        // mag_i, mag_j ≠ 0, hence positive.
        let mag_i_ne = mag_ne_zero(d, pp, sk_i, prime_proof, pos_i, ub_i);
        let mag_j_ne = mag_ne_zero(d, pp, sk_j, prime_proof, pos_j, ub_j);
        let mag_i_pos = pos_of_ne_zero(d, mag_i, mag_i_ne);
        let mag_j_pos = pos_of_ne_zero(d, mag_j, mag_j_ne);

        // Cancel the closing `- 1`: mag_i = mag_j.
        let sub_i = d.sub(mag_i, one_nat);
        let sub_j = d.sub(mag_j, one_nat);
        let succ_sub_i = d.succ(sub_i);
        let succ_sub_j = d.succ(sub_j);
        let cancel_i = d.lemma(p.nat.sub_add_cancel, &[one_nat, mag_i, mag_i_pos]);
        let cancel_j = d.lemma(p.nat.sub_add_cancel, &[one_nat, mag_j, mag_j_pos]);
        let succ_congr = d.congr(sub_i, sub_j, heq, &|d, x| d.succ(x));
        let cancel_i_rev = d.symm(succ_sub_i, mag_i, cancel_i);
        let (_, mag_eq) = d.chain(
            mag_i,
            &[
                (succ_sub_i, cancel_i_rev),
                (succ_sub_j, succ_congr),
                (mag_j, cancel_j),
            ],
        );

        // r_i = r_j (Int), hence `ModEq p pw_i pw_j` (definitionally).
        let r_i_nonneg = d.const_app(p.emod_nonneg, &[pw_i, big_p, ne_big_p]);
        let r_j_nonneg = d.const_app(p.emod_nonneg, &[pw_j, big_p, ne_big_p]);
        let bridge_i = d.const_app(p.of_nat_nat_abs_of_nonneg, &[r_i, r_i_nonneg]);
        let bridge_j = d.const_app(p.of_nat_nat_abs_of_nonneg, &[r_j, r_j_nonneg]);
        let ofnat_mag_i = d.of_nat(mag_i);
        let ofnat_mag_j = d.of_nat(mag_j);
        let congr_mag = d.nat_eq_to_int(mag_i, mag_j, mag_eq, &|d, y| d.of_nat(y));
        let bridge_i_rev = d.isymm(ofnat_mag_i, r_i, bridge_i);
        let (_, r_i_eq_r_j) = d.ichain(
            r_i,
            &[
                (ofnat_mag_i, bridge_i_rev),
                (ofnat_mag_j, congr_mag),
                (r_j, bridge_j),
            ],
        );

        // ModEq p (pw_i*a_i) one and ModEq p (pw_j*a_j) one, commuted.
        let mip_i = d.const_app(p.mul_inv_of_pow, &[pp, sk_i, prime_proof, pos_i, ub_i]);
        let mip_j = d.const_app(p.mul_inv_of_pow, &[pp, sk_j, prime_proof, pos_j, ub_j]);
        let comm_i = d.const_app(p.mul_comm, &[a_i, pw_i]);
        let ai_pwi = d.imul(a_i, pw_i);
        let pwi_ai = d.imul(pw_i, a_i);
        let mip_i_comm = d.int_eq_rewrite(ai_pwi, pwi_ai, comm_i, mip_i, &|d, x| {
            super::modeq::imodeq(d, big_p, x, one_i)
        });
        let comm_j = d.const_app(p.mul_comm, &[a_j, pw_j]);
        let aj_pwj = d.imul(a_j, pw_j);
        let pwj_aj = d.imul(pw_j, a_j);
        let mip_j_comm = d.int_eq_rewrite(aj_pwj, pwj_aj, comm_j, mip_j, &|d, x| {
            super::modeq::imodeq(d, big_p, x, one_i)
        });

        // ModEq p (pw_i*a_j)(pw_j*a_j), then trans with mip_j_comm.
        let pwi_aj = d.imul(pw_i, a_j);
        let pwj_aj = d.imul(pw_j, a_j);
        let cong2 = d.const_app(
            p.mod_eq_mul_right,
            &[big_p, pw_i, pw_j, a_j, pos_big_p, r_i_eq_r_j],
        );
        let mip_j_shifted = d.const_app(
            p.mod_eq_trans,
            &[big_p, pwi_aj, pwj_aj, one_i, cong2, mip_j_comm],
        );

        let uniq = d.const_app(
            p.mod_eq_inverse_unique,
            &[big_p, pw_i, a_i, a_j, pos_big_p, mip_i_comm, mip_j_shifted],
        );

        // Int.emod is the identity on both a_i and a_j: `uniq` forces
        // `Eq Int a_i a_j`.
        let a_i_nonneg = d.lemma(p.nat.zero_le, &[sk_i]);
        let a_j_nonneg = d.lemma(p.nat.zero_le, &[sk_j]);
        let emod_ai_eq = emod_eq_self_of_in_range(d, a_i, big_p, pos_big_p, a_i_nonneg, ub_i);
        let emod_aj_eq = emod_eq_self_of_in_range(d, a_j, big_p, pos_big_p, a_j_nonneg, ub_j);
        let emod_ai_raw = d.iemod(a_i, big_p);
        let emod_aj_raw = d.iemod(a_j, big_p);
        let emod_ai_rev = d.isymm(emod_ai_raw, a_i, emod_ai_eq);
        let (_, a_i_eq_a_j) = d.ichain(
            a_i,
            &[
                (emod_ai_raw, emod_ai_rev),
                (emod_aj_raw, uniq),
                (a_j, emod_aj_eq),
            ],
        );

        // `Int.natAbs` congruence: `succ i = succ j`, then `Nat.succ_injective`.
        let refl_sk_i = d.refl(sk_i);
        let nat_eq_final = d.int_eq_rewrite(a_i, a_j, a_i_eq_a_j, refl_sk_i, &|d, x| {
            let nx = {
                let f = p.nat_abs;
                d.const_app(f, &[x])
            };
            d.eq(sk_i, nx)
        });
        let succ_inj_fn = d.lemma(p.nat.succ_injective, &[i, j]);
        let i_eq_j = d.apply(succ_inj_fn, &[nat_eq_final]);

        let inner_body = {
            let with_heq = d.lam_fv(heq_fv, heq_ty, i_eq_j);
            let with_hj = d.lam_fv(hj_fv, hj_ty, with_heq);
            let with_hi = d.lam_fv(hi_fv, hi_ty, with_hj);
            let with_j = d.lam_fv(j_fv, nat, with_hi);
            d.lam_fv(i_fv, nat, with_j)
        };
        let proof = d.lam_fv(prime_fv, prime_ty, inner_body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Eq Nat (succ (sub pp two)) (sub pp one)`, given a primality proof for
/// `pp` — `succ(p-2) = p-1`. The same two-`Nat.sub_add_cancel`s-glued-by-
/// `Nat.succ_injective` derivation [`declare_mul_inv_of_pow`] already builds
/// inline; duplicated here (five lines) rather than extracted from under an
/// already-landed proof.
fn succ_pm2_eq_pm1(d: &mut IntDev<'_>, pp: ExprId, prime_proof: ExprId) -> ExprId {
    let p = d.int();
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let (two_le_ty, clause_ty) = prime_parts(d, pp);
    let two_le = d.and_left(two_le_ty, clause_ty, prime_proof);
    let one_le_pp = nat_prime_pos(d, pp, prime_proof);

    let pm2 = d.sub(pp, two_nat);
    let succ_pm2 = d.succ(pm2);
    let succ_succ_pm2 = d.succ(succ_pm2);
    let cancel2 = d.lemma(p.nat.sub_add_cancel, &[two_nat, pp, two_le]);
    let pm1 = d.sub(pp, one_nat);
    let succ_pm1 = d.succ(pm1);
    let cancel1 = d.lemma(p.nat.sub_add_cancel, &[one_nat, pp, one_le_pp]);
    let cancel1_rev = d.symm(succ_pm1, pp, cancel1);
    let combined = d.trans(succ_succ_pm2, pp, succ_pm1, cancel2, cancel1_rev);
    let succ_injective_fn = d.lemma(p.nat.succ_injective, &[succ_pm2, pm1]);
    d.apply(succ_injective_fn, &[combined])
}

/// `Nat.inverseIndex_fixed_point :
/// ∀ p k, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) → Lt k (p-1) →
///   Eq Nat (inverseIndex p k) k → Or (Eq Nat k zero) (Eq Nat k (p-2))`
///
/// **The fixed-point characterisation**: the only residues that are their own
/// modular inverse are `1` and `p-1` — equivalently, the only fixed indices
/// of `σ := Nat.inverseIndex p` are `0` and `p-2`. This is the converse of
/// the two direct computations `σ 0 = 0` / `σ (p-2) = p-2` (neither of which
/// is built here; both are immediate unfoldings this development has not
/// needed to name), and it is the theorem that says a pairing argument over
/// `σ` has exactly two exceptions — every route to Wilson's theorem needs it.
///
/// `Int.self_inverse_mod_prime` is the entire mathematical content
/// (`a*a ≡ 1 [p] ⟹ a ≡ ±1 [p]`, via `Int.euclid_lemma`); this transports it
/// across the index/residue correspondence `a := ofNat(k+1)`, `n := p-1`, the
/// same correspondence [`declare_inverse_index`] and
/// [`declare_inverse_index_injective`] already use.
///
/// Route: with `sk := succ k`, `a := ofNat sk`, `pw := a^(p-2)`,
/// `r := emod(pw, ofNat p)`, `mag := natAbs r` — exactly `inverseIndex`'s own
/// body at `(p, k)`, so the hypothesis `σ k = k` is definitionally
/// `mag - 1 = k`:
///
/// 1. `mag ≠ 0` ([`mag_ne_zero`], the same fact
///    [`declare_inverse_index_injective`] needs), hence `succ(mag-1) = mag`
///    (`Nat.sub_add_cancel`); combined with the hypothesis, `sk = mag`.
/// 2. `a = ofNat mag = r` (`Int.of_nat_nat_abs_of_nonneg`), and `r ≡ pw [p]`
///    always ([`emod_modeq_self`]), so `a ≡ pw [p]`; scaling
///    `Int.mul_inv_of_pow`'s `a*pw ≡ 1 [p]` by `a` on the left gives
///    `a*a ≡ 1 [p]`.
/// 3. `Int.self_inverse_mod_prime` at `(ofNat p, a)` needs `1 ≤ a ≤ p-1` over
///    `ℤ`: the lower bound is `Nat.zero_lt_succ` directly (`Int.le`/`Int.lt`
///    on `ofNat`-headed arguments reduce structurally to `Nat.le`/`Nat.lt`,
///    the same fact [`declare_inverse_index_maps_into`]'s doc records); the
///    upper bound needs the one genuinely new piece — `Eq Int (ofNat p - one)
///    (ofNat (p-1))` — built from `Int.add_neg_cancel_right` and
///    `Nat.sub_add_cancel` rather than the `subNatNat` borrow machinery,
///    since `Int.sub` unfolds transparently to `add a (neg b)` and needs no
///    case split on the (symbolic) magnitude.
/// 4. The conclusion `ModEq p a one ∨ ModEq p a (p-1)` decides which: each
///    canonical residue (`a`, `one`, and the rewritten `ofNat(p-1)`) is
///    already `emod`-idempotent in range ([`emod_eq_self_of_in_range`]), so
///    each disjunct collapses a `ModEq` into a literal `Eq Int`, then an
///    `Int.natAbs` congruence turns it into `Eq Nat sk 1` or `Eq Nat sk
///    (p-1)` — and `Nat.succ_injective` (the second case composed with
///    [`succ_pm2_eq_pm1`]) closes `Eq Nat k 0` or `Eq Nat k (p-2)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_inverse_index_fixed_point(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.inverse_index_fixed_point, 2, &|d, v| {
        let (pp, k) = (v[0], v[1]);
        let prime_ty = prime_condition(d, pp);

        let one_nat = d.num(1);
        let two_nat = d.num(2);
        let pm1 = d.sub(pp, one_nat);
        let pm2 = d.sub(pp, two_nat);
        let hk_ty = d.lt(k, pm1);
        let sigma_k = d.const_app(p.inverse_index, &[pp, k]);
        let heq_ty = d.eq(sigma_k, k);
        let zero_nat = d.zero();
        let is_zero = d.eq(k, zero_nat);
        let is_pm2 = d.eq(k, pm2);
        let concl = d.or(is_zero, is_pm2);

        let stmt = {
            let inner = d.arrow(heq_ty, concl);
            let with_hk = d.arrow(hk_ty, inner);
            d.arrow(prime_ty, with_hk)
        };

        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        let one_le_pp = nat_prime_pos(d, pp, prime_proof);
        let pos_big_p = one_le_pp;
        let succ_pm1 = d.succ(pm1);
        let cancel1 = d.lemma(p.nat.sub_add_cancel, &[one_nat, pp, one_le_pp]);
        let (two_le_ty, clause_ty) = prime_parts(d, pp);
        let two_le = d.and_left(two_le_ty, clause_ty, prime_proof);

        let big_p = d.of_nat(pp);
        let one_i = d.ione();

        // ub_k : Lt (succ k) pp, from hk : Lt k pm1.
        let sk = d.succ(k);
        let mono_fn = d.lemma(p.nat.succ_le_succ, &[sk, pm1]);
        let mono = d.apply(mono_fn, &[hk]);
        let ub_k = d.nat_rewrite(succ_pm1, pp, cancel1, mono, &|d, x| {
            let s = d.succ(sk);
            d.le(s, x)
        });
        let pos_sk = d.lemma(p.nat.zero_lt_succ, &[k]);

        // a, pw, r, mag — exactly `inverseIndex`'s own body at (pp, k).
        let a = d.of_nat(sk);
        let pw = d.ipow(a, pm2);
        let r = d.iemod(pw, big_p);
        let mag = {
            let f = p.nat_abs;
            d.const_app(f, &[r])
        };

        // mag ≠ 0, hence positive; succ(mag-1) = mag.
        let mag_ne = mag_ne_zero(d, pp, sk, prime_proof, pos_sk, ub_k);
        let mag_pos = pos_of_ne_zero(d, mag, mag_ne);
        let sub_mag = d.sub(mag, one_nat);
        let succ_sub_mag = d.succ(sub_mag);
        let cancel_mag = d.lemma(p.nat.sub_add_cancel, &[one_nat, mag, mag_pos]);

        // sk = mag, from heq : Eq Nat (inverseIndex pp k) k, defeq Eq Nat sub_mag k.
        let succ_congr = d.congr(sub_mag, k, heq, &|d, x| d.succ(x));
        let congr_rev = d.symm(succ_sub_mag, sk, succ_congr);
        let sk_eq_mag = d.trans(sk, succ_sub_mag, mag, congr_rev, cancel_mag);

        // a = ofNat mag = r.
        let a_eq_ofnat_mag = d.nat_eq_to_int(sk, mag, sk_eq_mag, &|d, y| d.of_nat(y));
        let ne_big_p = int_ne_zero_of_pos(d, big_p, pos_big_p);
        let r_nonneg = d.const_app(p.emod_nonneg, &[pw, big_p, ne_big_p]);
        let bridge = d.const_app(p.of_nat_nat_abs_of_nonneg, &[r, r_nonneg]);
        let ofnat_mag = d.of_nat(mag);
        let a_eq_r = d.itrans(a, ofnat_mag, r, a_eq_ofnat_mag, bridge);

        // a ≡ pw [p]: pw ≡ r [p] always, rewritten through a = r.
        let modeq_pw_r = emod_modeq_self(d, pw, big_p, pos_big_p);
        let r_eq_a = d.isymm(a, r, a_eq_r);
        let modeq_pw_a = d.int_eq_rewrite(r, a, r_eq_a, modeq_pw_r, &|d, x| {
            super::modeq::imodeq(d, big_p, pw, x)
        });
        let modeq_a_pw = d.const_app(p.mod_eq_symm, &[big_p, pw, a, modeq_pw_a]);

        // a*a ≡ 1 [p].
        let mip = d.const_app(p.mul_inv_of_pow, &[pp, sk, prime_proof, pos_sk, ub_k]);
        let scaled = d.const_app(p.mod_eq_mul_left, &[big_p, a, pw, a, pos_big_p, modeq_a_pw]);
        let aa = d.imul(a, a);
        let a_pw = d.imul(a, pw);
        let sq_modeq = d.const_app(p.mod_eq_trans, &[big_p, aa, a_pw, one_i, scaled, mip]);

        // Int.sub big_p one_i = ofNat pm1 — the one genuinely new piece: not a
        // `subNatNat` borrow (no case split on the symbolic magnitude), just
        // `Int.add_neg_cancel_right` applied to the Nat-derived `ofNat pm1 +
        // one_i = big_p`.
        let ofnat_pm1 = d.of_nat(pm1);
        let key = d.nat_eq_to_int(succ_pm1, pp, cancel1, &|d, y| d.of_nat(y));
        let sum_pm1_one = d.iadd(ofnat_pm1, one_i);
        let neg_one = d.ineg(one_i);
        let cancel_right = d.const_app(p.add_neg_cancel_right, &[ofnat_pm1, one_i]);
        let congr_key = d.icongr(sum_pm1_one, big_p, key, &|d, t| d.iadd(t, neg_one));
        let lhs_after = d.iadd(big_p, neg_one);
        let x_term = d.iadd(sum_pm1_one, neg_one);
        let congr_key_rev = d.isymm(x_term, lhs_after, congr_key);
        let sub_eq_pm1 = d.itrans(lhs_after, x_term, ofnat_pm1, congr_key_rev, cancel_right);
        let sub_big_p_one = d.isub(big_p, one_i);

        // ub_proof : Int.le a (Isub big_p one_i), from sk ≤ pm1 (Nat).
        let cancel1_rev = d.symm(succ_pm1, pp, cancel1);
        let ub_k_succ = d.nat_rewrite(pp, succ_pm1, cancel1_rev, ub_k, &|d, x| d.lt(sk, x));
        let le_fn = d.lemma(p.nat.le_of_lt_succ, &[sk, pm1]);
        let sk_le_pm1 = d.apply(le_fn, &[ub_k_succ]);
        let sub_eq_pm1_rev = d.isymm(sub_big_p_one, ofnat_pm1, sub_eq_pm1);
        let ub_proof = d.int_eq_rewrite(
            ofnat_pm1,
            sub_big_p_one,
            sub_eq_pm1_rev,
            sk_le_pm1,
            &|d, x| d.ile(a, x),
        );

        // Canonical-residue facts both branches need.
        let a_nonneg = d.lemma(p.nat.zero_le, &[sk]);
        let emod_a_eq = emod_eq_self_of_in_range(d, a, big_p, pos_big_p, a_nonneg, ub_k);
        let emod_a_raw = d.iemod(a, big_p);
        let emod_a_rev = d.isymm(emod_a_raw, a, emod_a_eq);
        let one_nonneg = d.lemma(p.nat.zero_le, &[one_nat]);
        let emod_one_eq = emod_eq_self_of_in_range(d, one_i, big_p, pos_big_p, one_nonneg, two_le);
        let emod_one_raw = d.iemod(one_i, big_p);
        let pm1_nonneg = d.lemma(p.nat.zero_le, &[pm1]);
        let one_pos = d.lemma(p.nat.zero_lt_succ, &[zero_nat]);
        let pm1_lt_pp = d.lemma(p.nat.sub_lt, &[pp, one_nat, one_le_pp, one_pos]);
        let emod_pm1_eq =
            emod_eq_self_of_in_range(d, ofnat_pm1, big_p, pos_big_p, pm1_nonneg, pm1_lt_pp);
        let emod_pm1_raw = d.iemod(ofnat_pm1, big_p);

        let disj = d.const_app(
            p.self_inverse_mod_prime,
            &[big_p, a, prime_proof, pos_big_p, pos_sk, ub_proof, sq_modeq],
        );
        let modeq_a_one_ty = super::modeq::imodeq(d, big_p, a, one_i);
        let modeq_a_pm1_ty = super::modeq::imodeq(d, big_p, a, sub_big_p_one);

        let on_left = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
            let (_, a_eq_one) = d.ichain(
                a,
                &[
                    (emod_a_raw, emod_a_rev),
                    (emod_one_raw, h),
                    (one_i, emod_one_eq),
                ],
            );
            let refl_sk = d.refl(sk);
            let nat_eq_sk1 = d.int_eq_rewrite(a, one_i, a_eq_one, refl_sk, &|d, x| {
                let nx = {
                    let f = p.nat_abs;
                    d.const_app(f, &[x])
                };
                d.eq(sk, nx)
            });
            let succ_inj_fn = d.lemma(p.nat.succ_injective, &[k, zero_nat]);
            let k_eq_zero = d.apply(succ_inj_fn, &[nat_eq_sk1]);
            d.or_inl(is_zero, is_pm2, k_eq_zero)
        };

        let on_right = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
            let h_pm1 = d.int_eq_rewrite(sub_big_p_one, ofnat_pm1, sub_eq_pm1, h, &|d, x| {
                super::modeq::imodeq(d, big_p, a, x)
            });
            let (_, a_eq_pm1) = d.ichain(
                a,
                &[
                    (emod_a_raw, emod_a_rev),
                    (emod_pm1_raw, h_pm1),
                    (ofnat_pm1, emod_pm1_eq),
                ],
            );
            let refl_sk = d.refl(sk);
            let nat_eq_sk_pm1 = d.int_eq_rewrite(a, ofnat_pm1, a_eq_pm1, refl_sk, &|d, x| {
                let nx = {
                    let f = p.nat_abs;
                    d.const_app(f, &[x])
                };
                d.eq(sk, nx)
            });
            let succ_pm2 = d.succ(pm2);
            let succ_pm2_pm1 = succ_pm2_eq_pm1(d, pp, prime_proof);
            let succ_pm2_pm1_rev = d.symm(succ_pm2, pm1, succ_pm2_pm1);
            let sk_eq_succ_pm2 = d.trans(sk, pm1, succ_pm2, nat_eq_sk_pm1, succ_pm2_pm1_rev);
            let succ_inj_fn = d.lemma(p.nat.succ_injective, &[k, pm2]);
            let k_eq_pm2 = d.apply(succ_inj_fn, &[sk_eq_succ_pm2]);
            d.or_inr(is_zero, is_pm2, k_eq_pm2)
        };

        let result = d.or_elim(
            modeq_a_one_ty,
            modeq_a_pm1_ty,
            concl,
            disj,
            on_left,
            on_right,
        );

        let inner_body = {
            let with_heq = d.lam_fv(heq_fv, heq_ty, result);
            d.lam_fv(hk_fv, hk_ty, with_heq)
        };
        let proof = d.lam_fv(prime_fv, prime_ty, inner_body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.inverseIndex_involutive :
/// ∀ p k, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) → Lt k (p-1) →
///   Eq Nat (inverseIndex p (inverseIndex p k)) k`
///
/// `σ := Nat.inverseIndex p` is its own inverse: applying it twice returns
/// the original index, for every `k` (fixed points included, unconditionally
/// — unlike [`declare_inverse_index_fixed_point`], this needs no hypothesis
/// about `k` being fixed). Route, with `sk := succ k`, `a := ofNat sk`,
/// `pw := a^(p-2)`, `r := emod(pw, ofNat p)`, `mag := natAbs r` —
/// `inverseIndex p k`'s own body, so `σ k` is definitionally `mag - 1`:
///
/// 1. `mag ≠ 0` ([`mag_ne_zero`]), hence `succ(mag - 1) = mag`
///    (`Nat.sub_add_cancel`); write `sk2 := succ(σ k)`, so `sk2 = mag`.
/// 2. `a2 := ofNat sk2` equals `r` exactly (`Int.of_nat_nat_abs_of_nonneg` at
///    `mag`, transported through `sk2 = mag`) — the same transport
///    [`declare_inverse_index_fixed_point`] uses, here unconditional.
/// 3. `mag < p` transports from `r`'s own `emod` bound exactly as
///    [`declare_inverse_index_maps_into`] does, giving `sk2 < p` through
///    `sk2 = mag`, so [`declare_mul_inv_of_pow`] applies at `sk2`:
///    `ModEq p (a2 * a2^(p-2)) 1` — `σ`'s second application's own pairing.
/// 4. `ModEq p (a * r) 1`, from [`declare_mul_inv_of_pow`] at `k` (`a*pw≡1`)
///    rewritten through `pw ≡ r [p]` ([`emod_modeq_self`]); rewritten again
///    through `a2 = r` (step 2) and commuted: `ModEq p (a2 * a) 1`.
/// 5. `Int.modEq_inverse_unique` at the common factor `a2` (steps 3 and 4:
///    both `a2^(p-2)` and `a` are inverses of `a2`) gives
///    `ModEq p (a2^(p-2)) a`; composed with `emod_modeq_self` at `a2^(p-2)`
///    gives `ModEq p r2 a`, where `r2 := emod(a2^(p-2), p)` is `σ(σ k)`'s own
///    residue. Both `r2` and `a` are canonical representatives in `[0,p)`
///    ([`emod_eq_self_of_in_range`]), so the congruence collapses to literal
///    equality `r2 = a`; an `Int.natAbs` congruence (the same
///    defeq-transparency trick [`declare_inverse_index_injective`] closes
///    with) plus `Nat.succ_injective` (composed with `mag ≠ 0` at `sk2`,
///    cancelling the closing `- 1` a second time) closes `Eq Nat (σ(σ k)) k`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_inverse_index_involutive(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.inverse_index_involutive, 2, &|d, v| {
        let (pp, k) = (v[0], v[1]);
        let prime_ty = prime_condition(d, pp);

        let one_nat = d.num(1);
        let two_nat = d.num(2);
        let pm1 = d.sub(pp, one_nat);
        let pm2 = d.sub(pp, two_nat);
        let hk_ty = d.lt(k, pm1);
        let sigma_k = d.const_app(p.inverse_index, &[pp, k]);
        let sigma_sigma_k = d.const_app(p.inverse_index, &[pp, sigma_k]);
        let concl = d.eq(sigma_sigma_k, k);

        let stmt = {
            let inner = d.arrow(hk_ty, concl);
            d.arrow(prime_ty, inner)
        };

        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);

        let one_le_pp = nat_prime_pos(d, pp, prime_proof);
        let pos_big_p = one_le_pp;
        let succ_pm1 = d.succ(pm1);
        let cancel1 = d.lemma(p.nat.sub_add_cancel, &[one_nat, pp, one_le_pp]);
        let big_p = d.of_nat(pp);
        let one_i = d.ione();
        let ne_big_p = int_ne_zero_of_pos(d, big_p, pos_big_p);

        // sk, a, pw, r, mag — exactly `inverseIndex`'s own body at (pp, k).
        let sk = d.succ(k);
        let mono_fn = d.lemma(p.nat.succ_le_succ, &[sk, pm1]);
        let mono = d.apply(mono_fn, &[hk]);
        let ub_k = d.nat_rewrite(succ_pm1, pp, cancel1, mono, &|d, x| {
            let s = d.succ(sk);
            d.le(s, x)
        });
        let pos_sk = d.lemma(p.nat.zero_lt_succ, &[k]);

        let a = d.of_nat(sk);
        let pw = d.ipow(a, pm2);
        let r = d.iemod(pw, big_p);
        let mag = {
            let f = p.nat_abs;
            d.const_app(f, &[r])
        };

        // mag ≠ 0, hence positive; succ(mag-1) = mag.
        let mag_ne = mag_ne_zero(d, pp, sk, prime_proof, pos_sk, ub_k);
        let mag_pos = pos_of_ne_zero(d, mag, mag_ne);
        let sk2 = d.succ(sigma_k); // succ(mag - 1), the second application's `succ k`.
        let cancel_mag = d.lemma(p.nat.sub_add_cancel, &[one_nat, mag, mag_pos]); // Eq Nat sk2 mag

        // mag < p, transported from r's own emod bound (as in
        // `declare_inverse_index_maps_into`).
        let r_nonneg = d.const_app(p.emod_nonneg, &[pw, big_p, ne_big_p]);
        let r_lt = d.const_app(p.emod_lt_of_pos, &[pw, big_p, pos_big_p]);
        let bridge = d.const_app(p.of_nat_nat_abs_of_nonneg, &[r, r_nonneg]); // Eq Int (ofNat mag) r
        let ofnat_mag = d.of_nat(mag);
        let bridge_rev = d.isymm(ofnat_mag, r, bridge); // Eq Int r (ofNat mag)
        let mag_lt_pp = d.int_eq_rewrite(r, ofnat_mag, bridge_rev, r_lt, &|d, x| d.ilt(x, big_p));
        // mag_lt_pp is usable, via defeq, as `Nat.lt mag pp`.

        // sk2 < p, sk2 positive.
        let mag_eq_sk2 = d.symm(sk2, mag, cancel_mag); // Eq Nat mag sk2
        let ub_sk2 = d.nat_rewrite(mag, sk2, mag_eq_sk2, mag_lt_pp, &|d, x| d.lt(x, pp));
        let pos_sk2 = d.lemma(p.nat.zero_lt_succ, &[sigma_k]);

        // a2 := ofNat sk2, equal to r exactly (through sk2 = mag = natAbs r).
        let a2 = d.of_nat(sk2);
        let a2_eq_ofnat_mag = d.nat_eq_to_int(sk2, mag, cancel_mag, &|d, y| d.of_nat(y));
        let a2_eq_r = d.itrans(a2, ofnat_mag, r, a2_eq_ofnat_mag, bridge);

        // Step 3: a2's own pairing, ModEq p (a2 * a2^(p-2)) 1.
        let pw2 = d.ipow(a2, pm2);
        let a2_pw2_modeq_one =
            d.const_app(p.mul_inv_of_pow, &[pp, sk2, prime_proof, pos_sk2, ub_sk2]);

        // Step 4: ModEq p (a * r) 1, from a * pw ≡ 1 rewritten through
        // pw ≡ r [p]; then ModEq p (a2 * a) 1, through a2 = r and mul_comm.
        let mip = d.const_app(p.mul_inv_of_pow, &[pp, sk, prime_proof, pos_sk, ub_k]);
        let modeq_pw_r = emod_modeq_self(d, pw, big_p, pos_big_p); // ModEq p pw r
        let scaled = d.const_app(p.mod_eq_mul_left, &[big_p, pw, r, a, pos_big_p, modeq_pw_r]);
        let a_pw = d.imul(a, pw);
        let a_r = d.imul(a, r);
        let scaled_symm = d.const_app(p.mod_eq_symm, &[big_p, a_pw, a_r, scaled]);
        let a_r_modeq_one =
            d.const_app(p.mod_eq_trans, &[big_p, a_r, a_pw, one_i, scaled_symm, mip]);

        let r_eq_a2 = d.isymm(a2, r, a2_eq_r); // Eq Int r a2
        let a_a2 = d.imul(a, a2);
        let a_a2_modeq_one = d.int_eq_rewrite(r, a2, r_eq_a2, a_r_modeq_one, &|d, x| {
            let lhs = d.imul(a, x);
            super::modeq::imodeq(d, big_p, lhs, one_i)
        });
        let mul_comm_pf = d.const_app(p.mul_comm, &[a, a2]);
        let a2_a = d.imul(a2, a);
        let a2_a_modeq_one = d.int_eq_rewrite(a_a2, a2_a, mul_comm_pf, a_a2_modeq_one, &|d, x| {
            super::modeq::imodeq(d, big_p, x, one_i)
        });

        // Step 5: modEq_inverse_unique at common factor a2.
        let pw2_a_modeq = d.const_app(
            p.mod_eq_inverse_unique,
            &[
                big_p,
                a2,
                pw2,
                a,
                pos_big_p,
                a2_pw2_modeq_one,
                a2_a_modeq_one,
            ],
        ); // ModEq p pw2 a

        let r2 = d.iemod(pw2, big_p);
        let modeq_pw2_r2 = emod_modeq_self(d, pw2, big_p, pos_big_p); // ModEq p pw2 r2
        let modeq_r2_pw2 = d.const_app(p.mod_eq_symm, &[big_p, pw2, r2, modeq_pw2_r2]);
        let r2_a_modeq = d.const_app(
            p.mod_eq_trans,
            &[big_p, r2, pw2, a, modeq_r2_pw2, pw2_a_modeq],
        );

        // Both r2 and a are canonical representatives in [0,p): collapse the
        // congruence to literal equality.
        let r2_nonneg = d.const_app(p.emod_nonneg, &[pw2, big_p, ne_big_p]);
        let r2_lt = d.const_app(p.emod_lt_of_pos, &[pw2, big_p, pos_big_p]);
        let emod_r2_eq = emod_eq_self_of_in_range(d, r2, big_p, pos_big_p, r2_nonneg, r2_lt);
        let a_nonneg = d.lemma(p.nat.zero_le, &[sk]);
        let emod_a_eq = emod_eq_self_of_in_range(d, a, big_p, pos_big_p, a_nonneg, ub_k);

        let emod_r2_raw = d.iemod(r2, big_p);
        let emod_a_raw = d.iemod(a, big_p);
        let emod_r2_rev = d.isymm(emod_r2_raw, r2, emod_r2_eq);
        let (_, r2_eq_a) = d.ichain(
            r2,
            &[
                (emod_r2_raw, emod_r2_rev),
                (emod_a_raw, r2_a_modeq),
                (a, emod_a_eq),
            ],
        );

        // Eq Nat sk mag2, via the natAbs-transparency trick.
        let a_eq_r2 = d.isymm(r2, a, r2_eq_a);
        let refl_sk = d.refl(sk);
        let mag2 = {
            let f = p.nat_abs;
            d.const_app(f, &[r2])
        };
        let sk_eq_mag2 = d.int_eq_rewrite(a, r2, a_eq_r2, refl_sk, &|d, x| {
            let nx = {
                let f = p.nat_abs;
                d.const_app(f, &[x])
            };
            d.eq(sk, nx)
        });

        // mag2 ≠ 0; succ(mag2 - 1) = mag2; combine to close.
        let mag2_ne = mag_ne_zero(d, pp, sk2, prime_proof, pos_sk2, ub_sk2);
        let mag2_pos = pos_of_ne_zero(d, mag2, mag2_ne);
        let sub_mag2 = d.sub(mag2, one_nat);
        let succ_sub_mag2 = d.succ(sub_mag2);
        let cancel_mag2 = d.lemma(p.nat.sub_add_cancel, &[one_nat, mag2, mag2_pos]);
        let cancel_mag2_rev = d.symm(succ_sub_mag2, mag2, cancel_mag2);
        let sk_eq_succ = d.trans(sk, mag2, succ_sub_mag2, sk_eq_mag2, cancel_mag2_rev);
        let succ_inj_fn = d.lemma(p.nat.succ_injective, &[k, sub_mag2]);
        let k_eq_result = d.apply(succ_inj_fn, &[sk_eq_succ]);
        let result = d.symm(k, sub_mag2, k_eq_result);

        let inner_body = d.lam_fv(hk_fv, hk_ty, result);
        let proof = d.lam_fv(prime_fv, prime_ty, inner_body);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// The collapse lemma, landed 2026-08-24 — and what it does NOT close.
//
// The module doc above promised the *pairing* collapse: every index other
// than the two fixed points (`k=0`, i.e. `a=1`, and `k=p-2`, i.e. `a=p-1`)
// pairs with a DISTINCT partner under `σ := Nat.inverseIndex p`, the pair's
// product is `1 [p]`, and the interior product collapses to `1 [p]`, leaving
// `factorial(p-1) ≡ 1*(p-1) ≡ -1 [p]`. Landing THAT argument needs a fresh
// induction that removes a matched pair from the range at a time — the same
// difficulty `Int.prodRange_permute` itself took three drafts to close
// (`point_override` + `prodRange_swap` + `Nat.restrict_injective`/
// `restrict_maps_into`, generalizing the motive over an EVOLVING self-map).
// The characterization lemma this needed to know in advance which index is
// which case — `σ k = k → k = 0 ∨ k = p-2`, the converse of the two direct
// computations `σ 0 = 0` / `σ (p-2) = p-2` — is now built and axiom-free:
// `Nat.inverseIndex_fixed_point` (`declare_inverse_index_fixed_point`, above).
// The swap/override induction itself is a SECOND induction of comparable
// size to `prodRange_permute`'s own, and it is NOT built here.
//
// What IS built, and is genuinely new inductive content rather than
// plumbing: `Int.prodRange_mul` (`prod.rs`) and `Int.modEq_prodRange_lt`
// (`prod.rs`) are both fresh inductions, and together with
// `Int.prodRange_permute` (already landed) and [`declare_mul_inv_of_pow`]
// they prove `Int.factorial_sq_modeq_one` below: **`((p-1)!)^2 ≡ 1 [p]`**,
// for every prime `p`. The route sidesteps the pairing/fixed-point argument
// entirely by using a fact the pairing argument does NOT need: for every
// `k < p-1`, `a_(σ k) = emod(a_k^(p-2), p)` EXACTLY (from `inverseIndex`'s
// own definition, no case split on whether `k` is a fixed point), so
// `a_k * a_(σ k) ≡ 1 [p]` holds for literally every index, fixed points
// included — squaring the *whole* permuted product costs no fixed-point
// bookkeeping at all.
//
// `((p-1)!)^2 ≡ 1 [p]` is real progress — combined with
// [`declare_self_inverse_mod_prime`] (applied to `emod(factorial(p-1), p)`,
// which is what actually satisfies that lemma's `1 ≤ a ≤ p-1` bound; the
// factorial itself does not) it would pin `factorial(p-1) ≡ ±1 [p]` — but a
// square root has two signs, and squaring is EXACTLY the operation that
// forgets which one. `Int.wilson` needs `factorial(p-1) ≡ -1 [p]`
// specifically, not `≡ ±1`; nothing below decides the sign, and the sign is
// where the actual mathematical content of Wilson's theorem lives (a
// composite `n` has no such obstruction, so `(n-1)! ≡ -1 [n]`'s FAILURE for
// composite `n` is precisely what a sign-blind fact could never certify).
// `Int.wilson` is NOT declared here; see this module's doc above for what
// full closure would still need.
// ============================================================================

/// `ModEq n x (emod x n)`, given `0 < n` — a value is always congruent to its
/// own canonical remainder. `emod x n` is already in `[0, n)`
/// (`emod_nonneg`/`emod_lt_of_pos`), so [`emod_eq_self_of_in_range`] applied
/// to `emod x n` itself gives `emod (emod x n) n = emod x n`; `ModEq n x
/// (emod x n)` unfolds (by `Int.ModEq`'s own definition) to exactly the
/// `Eq Int (emod x n) (emod (emod x n) n)` that is the `symm` of that fact.
fn emod_modeq_self(d: &mut IntDev<'_>, x: ExprId, n: ExprId, n_pos: ExprId) -> ExprId {
    let p = d.int();
    let ne_n = int_ne_zero_of_pos(d, n, n_pos);
    let exn = d.iemod(x, n);
    let r_nonneg = d.const_app(p.emod_nonneg, &[x, n, ne_n]);
    let r_lt = d.const_app(p.emod_lt_of_pos, &[x, n, n_pos]);
    let idem = emod_eq_self_of_in_range(d, exn, n, n_pos, r_nonneg, r_lt); // Eq Int (emod exn n) exn
    let emod_exn_n = d.iemod(exn, n);
    d.isymm(emod_exn_n, exn, idem)
}

/// `Eq Int (prodRange one_fn n) one`, for `one_fn := fun _ => Int.one` — a
/// constant-one product is `one`. Induction on `n`: the base case is
/// `prodRange_zero`'s own `Eq.refl`; the successor step is `mul_one` applied
/// to the induction hypothesis (`prodRange one_fn (succ j)` unfolds to
/// `mul (prodRange one_fn j) (one_fn j)`, and `one_fn j` is defeq `one`
/// regardless of `j`, the same beta-transparency
/// [`declare_prod_range_mul`](super::prod::declare_prod_range_mul)'s base
/// case leans on).
fn prod_range_const_one(d: &mut IntDev<'_>, one_fn: ExprId, n: ExprId) -> ExprId {
    let p = d.int();
    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let pr = d.const_app(p.prod_range, &[one_fn, x]);
        let one_i = d.ione();
        d.ieq(pr, one_i)
    };
    d.induct(
        &motive,
        &|d| {
            let one_i = d.ione();
            d.irefl(one_i)
        },
        &|d, j, ih| {
            let one_i = d.ione();
            let pr_j = d.const_app(p.prod_range, &[one_fn, j]);
            let start = d.imul(pr_j, one_i);
            let mid = d.imul(one_i, one_i);
            let step1 = d.icongr(pr_j, one_i, ih, &|d, t| d.imul(t, one_i));
            let mul_one_pf = d.const_app(p.mul_one, &[one_i]);
            let (_e, proof) = d.ichain(start, &[(mid, step1), (one_i, mul_one_pf)]);
            proof
        },
        n,
    )
}

/// `Int.factorial_sq_modeq_one :
/// ∀ p, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) →
///   ModEq (ofNat p) (mul (factorial (p-1)) (factorial (p-1))) one`
///
/// **The collapse lemma this slice lands** — see the module section above
/// this declaration for what it proves, why it sidesteps the pairing
/// argument, and exactly what is still missing for `Int.wilson`.
///
/// Route, with `n := p-1`, `σ := Nat.inverseIndex p`, `F := fun k =>
/// ofNat(succ k)` (the lambda `Int.factorial` itself unfolds to), `G := fun
/// k => F(σ k)`:
///
/// 1. `Int.prodRange_permute` at `F`, `σ`, `n` (fed
///    [`declare_inverse_index_injective`]/[`declare_inverse_index_maps_into`]):
///    `Eq Int (prodRange F n) (prodRange G n)`.
/// 2. For every `k < n`: `mag_k := natAbs(emod(F(k)^(p-2), ofNat p))` is
///    positive ([`mag_ne_zero`] + [`pos_of_ne_zero`]), so `succ(mag_k - 1) =
///    mag_k` (`Nat.sub_add_cancel`) — and `σ k` UNFOLDS to exactly
///    `mag_k - 1`, so `F(σ k) = ofNat(mag_k) = emod(F(k)^(p-2), ofNat p)`
///    (`of_nat_nat_abs_of_nonneg`), i.e. `G k` is EXACTLY that canonical
///    remainder, no case split on whether `k` is a fixed point. Combined
///    with [`emod_modeq_self`] (`emod(F(k)^(p-2),p) ≡ F(k)^(p-2) [p]`) and
///    [`declare_mul_inv_of_pow`] (`F(k) * F(k)^(p-2) ≡ 1 [p]`):
///    `ModEq (ofNat p) (mul (F k) (G k)) one`, for every `k < n`.
/// 3. `Int.prodRange_mul` at `F`, `G`, `n`: `Eq Int (prodRange (fun k => mul
///    (F k) (G k)) n) (mul (prodRange F n) (prodRange G n))`.
/// 4. `Int.modEq_prodRange_lt` at step 2's pointwise congruence:
///    `ModEq (ofNat p) (prodRange (fun k => mul (F k)(G k)) n) (prodRange
///    (fun _ => one) n)`, and [`prod_range_const_one`] collapses the RHS to
///    `one` exactly.
/// 5. Chaining 1, 3, 4 (rewriting `G`'s range back to `F`'s via step 1's
///    equality) gives `ModEq (ofNat p) (mul (prodRange F n) (prodRange F n))
///    one`, which is the goal up to the `Int.factorial`/`Int.prodRange`
///    defeq [`declare_factorial`] already relies on.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_factorial_sq_modeq_one(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    d.theorem(p.factorial_sq_modeq_one, 1, &|d, v| {
        let pp = v[0];
        let prime_ty = prime_condition(d, pp);

        let one_nat = d.num(1);
        let two_nat = d.num(2);
        let n = d.sub(pp, one_nat); // p - 1
        let big_p = d.of_nat(pp);
        let one_i = d.ione();
        let factorial_n = d.const_app(p.factorial, &[n]);
        let sq = d.imul(factorial_n, factorial_n);
        let concl = super::modeq::imodeq(d, big_p, sq, one_i);
        let stmt = d.arrow(prime_ty, concl);

        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);

        // F := fun k => ofNat (succ k) — the lambda `Int.factorial` unfolds to.
        let f_lambda = |d: &mut IntDev<'_>| -> ExprId {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sk = d.succ(k);
            let body = d.of_nat(sk);
            d.lam_fv(k_fv, nat, body)
        };
        let big_f = f_lambda(d);

        // sigma := fun k => Nat.inverseIndex pp k.
        let sigma = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let body = d.const_app(p.inverse_index, &[pp, k]);
            d.lam_fv(k_fv, nat, body)
        };
        let inj_sigma = d.const_app(p.inverse_index_injective, &[pp, prime_proof]);
        let maps_sigma = d.const_app(p.inverse_index_maps_into, &[pp, prime_proof]);

        // G := fun k => F (sigma k).
        let big_g = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sk = d.apply(sigma, &[k]);
            let body = d.apply(big_f, &[sk]);
            d.lam_fv(k_fv, nat, body)
        };

        // Step 1: prodRange F n = prodRange G n.
        let permute_eq = d.const_app(
            p.prod_range_permute,
            &[big_f, n, sigma, inj_sigma, maps_sigma],
        );

        let one_le_pp = nat_prime_pos(d, pp, prime_proof); // also `Int.lt zero_i big_p`, by defeq
        let pos_big_p = one_le_pp;
        let succ_n = d.succ(n);
        let cancel1 = d.lemma(p.nat.sub_add_cancel, &[one_nat, pp, one_le_pp]); // Eq Nat succ_n pp

        // Step 2: pointwise congruence, ∀ k, Lt k n → ModEq big_p (mul (F k) (G k)) one.
        let pointwise_pf = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);
            let hk_ty = d.lt(k, n);

            let sk = d.succ(k);
            let fk = d.of_nat(sk);

            // ub_k : Lt (succ k) pp ; pos_sk : Lt zero (succ k).
            let mono_fn = d.lemma(p.nat.succ_le_succ, &[sk, n]);
            let mono = d.apply(mono_fn, &[hk]);
            let ub_k = d.nat_rewrite(succ_n, pp, cancel1, mono, &|d, x| {
                let s = d.succ(sk);
                d.le(s, x)
            });
            let pos_sk = d.lemma(p.nat.zero_lt_succ, &[k]);

            // mip_k : ModEq big_p (mul fk pw_k) one.
            let mip_k = d.const_app(p.mul_inv_of_pow, &[pp, sk, prime_proof, pos_sk, ub_k]);

            let pm2 = d.sub(pp, two_nat);
            let pw_k = d.ipow(fk, pm2);
            let r_k = d.iemod(pw_k, big_p);
            let mag_k = {
                let f = p.nat_abs;
                d.const_app(f, &[r_k])
            };

            // mag_k ≠ 0, hence positive; succ(mag_k - 1) = mag_k.
            let mag_k_ne = mag_ne_zero(d, pp, sk, prime_proof, pos_sk, ub_k);
            let mag_k_pos = pos_of_ne_zero(d, mag_k, mag_k_ne);
            let sk_raw = d.sub(mag_k, one_nat);
            let succ_sk_raw = d.succ(sk_raw);
            let cancel_k = d.lemma(p.nat.sub_add_cancel, &[one_nat, mag_k, mag_k_pos]);
            // cancel_k : Eq Nat succ_sk_raw mag_k

            let ne_big_p = int_ne_zero_of_pos(d, big_p, pos_big_p);
            let r_k_nonneg = d.const_app(p.emod_nonneg, &[pw_k, big_p, ne_big_p]);

            let ofnat_succ_sk_raw = d.of_nat(succ_sk_raw);
            let ofnat_mag_k = d.of_nat(mag_k);
            let bridge_a = d.nat_eq_to_int(succ_sk_raw, mag_k, cancel_k, &|d, y| d.of_nat(y));
            let bridge_b = d.const_app(p.of_nat_nat_abs_of_nonneg, &[r_k, r_k_nonneg]);
            // F(sigma k) = ofNat(succ_sk_raw) = ofNat(mag_k) = r_k.
            let f_sk_eq_rk = d.itrans(ofnat_succ_sk_raw, ofnat_mag_k, r_k, bridge_a, bridge_b);

            // pw_k ≡ r_k [p] (emod is always congruent to its argument); rewrite
            // to get F(sigma k) ≡ pw_k [p].
            let modeq_pwk_rk = emod_modeq_self(d, pw_k, big_p, pos_big_p);
            let f_sk_eq_rk_rev = d.isymm(ofnat_succ_sk_raw, r_k, f_sk_eq_rk);
            let modeq_pwk_fsk = d.int_eq_rewrite(
                r_k,
                ofnat_succ_sk_raw,
                f_sk_eq_rk_rev,
                modeq_pwk_rk,
                &|d, x| super::modeq::imodeq(d, big_p, pw_k, x),
            );
            let modeq_fsk_pwk = d.const_app(
                p.mod_eq_symm,
                &[big_p, pw_k, ofnat_succ_sk_raw, modeq_pwk_fsk],
            );

            // Scale by fk on the left: ModEq big_p (mul fk (F(sigma k))) (mul fk pw_k).
            let scaled = d.const_app(
                p.mod_eq_mul_left,
                &[big_p, ofnat_succ_sk_raw, pw_k, fk, pos_big_p, modeq_fsk_pwk],
            );
            let lhs_scaled = d.imul(fk, ofnat_succ_sk_raw);
            let mid_scaled = d.imul(fk, pw_k);
            let final_pf = d.const_app(
                p.mod_eq_trans,
                &[big_p, lhs_scaled, mid_scaled, one_i, scaled, mip_k],
            );

            let with_hk = d.lam_fv(hk_fv, hk_ty, final_pf);
            d.lam_fv(k_fv, nat, with_hk)
        };

        // Step 3: prodRange (fun k => F k * G k) n = mul (prodRange F n) (prodRange G n).
        let prod_mul_eq = d.const_app(p.prod_range_mul, &[big_f, big_g, n]);

        // Step 4: prodRange (fun k => F k * G k) n ≡ prodRange (fun _ => one) n [p], = one.
        let one_lambda = {
            let k_fv = d.fresh_fvar();
            d.lam_fv(k_fv, nat, one_i)
        };
        let big_h = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let fk = d.apply(big_f, &[k]);
            let gk = d.apply(big_g, &[k]);
            let body = d.imul(fk, gk);
            d.lam_fv(k_fv, nat, body)
        };
        let const_one_pf = d.const_app(
            p.mod_eq_prod_range_lt,
            &[big_p, big_h, one_lambda, n, pos_big_p, pointwise_pf],
        );
        let prod_range_one_eq_one = prod_range_const_one(d, one_lambda, n);
        let h_range = d.const_app(p.prod_range, &[big_h, n]);
        let one_range = d.const_app(p.prod_range, &[one_lambda, n]);
        let modeq_h_one = d.int_eq_rewrite(
            one_range,
            one_i,
            prod_range_one_eq_one,
            const_one_pf,
            &|d, x| super::modeq::imodeq(d, big_p, h_range, x),
        );

        // Step 5: assemble, rewriting H's range to F*G's range and G's range
        // back to F's range.
        let f_range = d.const_app(p.prod_range, &[big_f, n]);
        let g_range = d.const_app(p.prod_range, &[big_g, n]);
        let mul_fg = d.imul(f_range, g_range);
        let modeq_mulfg_one =
            d.int_eq_rewrite(h_range, mul_fg, prod_mul_eq, modeq_h_one, &|d, x| {
                super::modeq::imodeq(d, big_p, x, one_i)
            });
        let permute_eq_rev = d.isymm(f_range, g_range, permute_eq);
        let modeq_ff_one = d.int_eq_rewrite(
            g_range,
            f_range,
            permute_eq_rev,
            modeq_mulfg_one,
            &|d, x| {
                let lhs = d.imul(f_range, x);
                super::modeq::imodeq(d, big_p, lhs, one_i)
            },
        );

        let proof = d.lam_fv(prime_fv, prime_ty, modeq_ff_one);
        (stmt, proof)
    })?;
    Ok(())
}
