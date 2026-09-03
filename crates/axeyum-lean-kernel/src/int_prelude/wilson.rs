//! **`Int.wilson` is proved, axiom-free, as of 2026-08-24: `p` prime ⟹
//! `(p-1)! ≡ -1 [p]`.** (`declare_wilson`, at the bottom of this file.) The
//! assembly this doc used to describe as remaining is done: `σ :=
//! Nat.inverseIndex p`'s interior reindexes down to
//! `Int.prod_range_pairing_collapse`'s own `[0,n)` shape
//! (`Int.factorial_interior_modeq_one`, via the new `Int.prodRange_shiftFront`
//! peeling the FRONT term of a `prodRange`), and the two boundary survivors
//! `1` and `p-1` close it (`Int.wilson`'s own doc section, near the bottom,
//! has the full route including the one place — relating `p-2` to `p-3` —
//! that needs `p ≥ 3` as its own case, with `p = 2` closed separately and
//! trivially since the interior is empty there). See the "`Int.wilson` — the
//! assembly" section below for the exact route, and
//! `wilson_concludes_the_negative_residue_under_primality`
//! (`int_prelude_tests.rs`) for the pinned statement — its own doc explains
//! why the axiom footprint alone cannot distinguish this from the FALSE
//! `+1`-concluding or `0 < p`-hypothesis'd statements.
//!
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
//! the same day, `Nat.inverseIndex_involutive` (`σ` is its own inverse). And,
//! also 2026-08-24: `Int.prod_range_pairing_collapse`, the interior-collapse
//! induction itself (see "The interior collapse", below) — a fixed-point-free
//! involution pairing up a domain, with every pair's product `≡ 1`, collapses
//! the whole `prodRange` to `1`. And, still 2026-08-24: the two direct
//! computations this file's own doc had named but never built —
//! `Nat.inverseIndex_fixes_zero` (`σ 0 = 0`) and `Nat.inverseIndex_fixes_last`
//! (`σ (p-2) = p-2`) — plus `Nat.inverseIndex_interior_fixed_point_free`, the
//! immediate contrapositive of `inverseIndex_fixed_point` on `0 < k < p-2`.
//! **Update, later still 2026-08-24: `Int.prod_range_pairing_collapse` now
//! DOES wire into Wilson's own `σ := Nat.inverseIndex p`** — see
//! `Int.factorial_interior_modeq_one` and `Int.wilson` below.
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
//! ## The interior collapse: `Int.prod_range_pairing_collapse`, landed 2026-08-24
//!
//! The *collapse* argument Wilson's theorem needs on top of the permutation
//! — "a fixed-point-free involution pairing up `[0,n)`, with every pair's
//! product `≡ 1`, collapses the whole `prodRange` to `1`" — is now proved,
//! axiom-free, as its own reusable lemma: `Int.prod_range_pairing_collapse`
//! (`∀ bigp, 0 < bigp → ∀ n F σ, InjectiveOn σ n → MapsInto σ n →
//! (∀k<n, σk≠k) → (∀k<n, σ(σk)=k) → (∀k<n, ModEq bigp (F k * F(σ k)) one) →
//! ModEq bigp (prodRange F n) one`, declared at the bottom of this file).
//!
//! Two design choices differ from the plan this doc previously carried,
//! discovered while actually building it:
//!
//! - **No `WellFounded.fix`.** The step always decreases the domain by
//!   exactly 2, so ordinary two-step structural induction suffices: prove
//!   `And (family n) (family (succ n))` together by plain `Nat.rec`, and the
//!   step case's `family (succ n)` component is available for free from the
//!   IH's right half, while the real work — `family (succ (succ m))` from
//!   `family m` — reads off the IH's LEFT half. No well-founded recursion
//!   principle, no second induction scheme.
//! - **No conjugation via `prod.rs`'s `point_swap`+`restrict_pair`.** The
//!   step (`family_succ_succ_proof`, `case_a_body`/`case_b_body`) locates
//!   `i0 := σ(succ m)`, the top index's partner (`σ i0 = succ m` for free by
//!   involution). If `i0 = m` the pair is already at the top: peel it via two
//!   `prodRange_succ` unfoldings and recurse directly (`peel_and_close`,
//!   shared by both cases — its `MapsInto`-on-the-smaller-domain half is the
//!   one genuine closure argument, via injectivity excluding the two removed
//!   positions). Otherwise (`i0 < m`) conjugate `σ` by a two-point swap
//!   `τ := tau_raw i0 m` — a **local, `IntDev`-native** copy of
//!   `Nat.transposition`'s own four-`Nat.ble`-cut construction and its five
//!   correctness facts (`tau_level2/3/4`, `tau_eq_lt_i`/`_at_i`/`_between`/
//!   `_at_j`/`_gt_j`, `tau_involutive_forall`, `tau_maps_into_forall`) rather
//!   than `nat_prelude/transposition.rs`'s own `Nat.transposition`: that
//!   file's helpers are typed concretely over `NatDev`, not generic over
//!   `NatOps`, so they are not callable from `IntDev` without a signature
//!   change to a file another lane may be editing. `σ' := τ∘σ∘τ`'s
//!   `InjectiveOn`/`MapsInto` come from the PUBLIC, already-generic
//!   `Nat.conjugate_injective`/`conjugate_maps_into`
//!   (`nat_prelude/transposition.rs`) fed this local `τ`; its
//!   fixed-point-freeness, involution, and the conjugated pairwise congruence
//!   are each a few lines of `τ∘τ = id` cancellation (`case_b_body`). The
//!   product side reuses `int_prelude/prod.rs`'s existing `Int`-valued
//!   `point_swap` and its `general_swap_agree` (both exposed `pub(super)` for
//!   this) plus `Int.prodRange_swap` directly — no new `Int`-valued swap
//!   machinery was needed, only the `Nat`-valued one for the index side.
//!
//! **Landed, later still 2026-08-24**: the wiring from this generic lemma to
//! Wilson's own `σ := Nat.inverseIndex p`. `σ 0 = 0` and `σ (p-2) = p-2` are
//! named equations (`declare_inverse_index_fixes_zero`/`_fixes_last`, above),
//! and `Nat.inverseIndex_interior_fixed_point_free` gives fixed-point-freeness
//! on the interior directly. The reindex of the interior domain `{1,…,p-3}`
//! down to `prod_range_pairing_collapse`'s own `[0,n)` shape went through
//! `Int.prodRange_shiftFront` (`prod.rs`, peeling the FRONT term of a
//! `prodRange`, general — no primality, no side condition) plus a per-index
//! bundle of facts about `σ' i := σ(i+1) - 1` (`sigma_prime_at`, below,
//! `InjectiveOn` derived generically from involution rather than transported
//! from `σ`'s own), landing `Int.factorial_interior_modeq_one`. `Int.wilson`
//! itself needed one more genuinely new piece: relating `p-2` to `p-3` (the
//! front-peel's own domain shift) only holds when `p ≥ 3`, so the ONE case
//! split in the whole assembly is there, with `p = 2` closed separately (the
//! interior is empty, `prodRange_zero` alone suffices — no reindex needed).
//! See "`Int.wilson` — the assembly", near the bottom of this file.
//!
//! The rearrangement principle Wilson's theorem needs beyond the collapse
//! lemma is `Int.prodRange_permute` (`prod.rs`) : `∀ f σ n, InjectiveOn σ n →
//! MapsInto σ n →
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
pub(super) fn prime_condition(d: &mut IntDev<'_>, magnitude: ExprId) -> ExprId {
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
/// `Eq Int ((a-1)*(a+1)) (a*a - 1)`, by `ring::int::prove_eq_at`
/// (ring-tactic-2, ADR-1582) rather than the hand chain this file used to
/// carry — including its own `cancel_common_addend` step, which is now
/// `ring::int::Problem::cancel_pairs`, found the hard way retiring exactly
/// this target (see ADR-1582).
fn diff_of_squares(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let p = d.int();
    crate::ring::int::prove_eq_at(d, &p, &[a], &|d, v| {
        let a = v[0];
        let one = d.ione();
        let sub_a1 = d.isub(a, one);
        let add_a1 = d.iadd(a, one);
        let lhs = d.imul(sub_a1, add_a1);
        let aa = d.imul(a, a);
        let rhs = d.isub(aa, one);
        (lhs, rhs)
    })
    .expect("diff_of_squares: (a-1)*(a+1) = a*a - 1 is a ring identity")
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
pub(super) fn prime_parts(d: &mut IntDev<'_>, magnitude: ExprId) -> (ExprId, ExprId) {
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
pub(super) fn nat_prime_pos(d: &mut IntDev<'_>, magnitude: ExprId, prime_proof: ExprId) -> ExprId {
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
pub(super) fn int_ne_zero_of_pos(d: &mut IntDev<'_>, x: ExprId, pos: ExprId) -> ExprId {
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
pub(super) fn emod_eq_self_of_in_range(
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
pub(super) fn pos_of_ne_zero(d: &mut IntDev<'_>, n: ExprId, hne: ExprId) -> ExprId {
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

/// `ModEq p (-1) (p-1)`, given `0 < p` — from `Int.dvd_refl p` transported
/// along `cancel_neg_add p one : (p + (-1)) + 1 = p`. The same standalone
/// fact [`declare_self_inverse_mod_prime`]'s `on_right` branch builds inline
/// (there, under a hypothesis it does not actually use to build this piece);
/// factored out here since [`declare_inverse_index_fixes_last`] needs it
/// unconditionally.
pub(super) fn neg_one_modeq_p_minus_one(
    d: &mut IntDev<'_>,
    big_p: ExprId,
    pos_big_p: ExprId,
) -> ExprId {
    let p = d.int();
    let one_i = d.ione();
    let neg_one = d.ineg(one_i);
    let p_minus_one = d.isub(big_p, one_i);

    let dvd_refl_p = d.const_app(p.dvd_refl, &[big_p]);
    let cna = super::modeq::cancel_neg_add(d, big_p, one_i);
    let cna_lhs = {
        let inner = d.iadd(big_p, neg_one);
        d.iadd(inner, one_i)
    };
    let reversed = d.isymm(cna_lhs, big_p, cna);
    let motive2 = d.ieq_motive(big_p, &|d, x| super::dvd::idvd(d, big_p, x));
    let result_r2 = d.itransport(big_p, motive2, dvd_refl_p, cna_lhs, reversed);

    let modeq_negone_pm1_ty = super::modeq::imodeq(d, big_p, neg_one, p_minus_one);
    let pm1_minus_negone = d.isub(p_minus_one, neg_one);
    let dvd_r2_ty = super::dvd::idvd(d, big_p, pm1_minus_negone);
    let iff_r2 = d.const_app(p.mod_eq_iff_dvd, &[big_p, neg_one, p_minus_one, pos_big_p]);
    let mpr_r2 = d.const_app(p.logic.iff_mpr, &[modeq_negone_pm1_ty, dvd_r2_ty, iff_r2]);
    d.apply(mpr_r2, &[result_r2])
}

/// `Nat.inverseIndex_fixes_zero :
/// ∀ p, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) → Eq Nat (inverseIndex p zero) zero`
///
/// The direct computation the module doc above and
/// [`declare_inverse_index_fixed_point`]'s own doc both name but do not
/// build: `1` is its own modular inverse, i.e. `σ 0 = 0` (`σ :=
/// Nat.inverseIndex p`). With `a := ofNat one` (`one := succ zero`, the
/// residue at index `0`) and `pw := a^(p-2)`:
///
/// `a` is `Int.one` up to a single delta-unfold (`Int.one := Int.ofNat 1`,
/// `defs.rs`), so `a*a = a = one` closes by `Int.mul_one` plus that one
/// bridging step, and `ModEq p (a*a) one` retypes `Int.ModEq.refl` at `one`
/// directly (the same unfold again, through `Int.ModEq`'s own definitional
/// layer). [`declare_mul_inv_of_pow`] gives `ModEq p (a*pw) one` at this same
/// `a`, and `Int.modEq_inverse_unique` (both `pw` and `a` are inverses of
/// `a`) collapses them to `ModEq p pw a`. `Int.emod` is the identity on both
/// canonical representatives — `pw`'s own residue and `a` itself
/// ([`emod_eq_self_of_in_range`]) — so that forces the literal `Eq Int r a`
/// (`r := emod(pw, ofNat p)`), and the `Int.natAbs` transparency trick
/// [`declare_inverse_index_fixed_point`] closes with turns it into `Eq Nat
/// one (natAbs r)` — exactly `inverseIndex p zero`'s own magnitude, so
/// `1 - 1 = 0` (a closed computation) finishes the goal.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_inverse_index_fixes_zero(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.inverse_index_fixes_zero, 1, &|d, v| {
        let pp = v[0];
        let prime_ty = prime_condition(d, pp);

        let one_nat = d.num(1);
        let two_nat = d.num(2);
        let zero_nat = d.zero();
        let sigma_zero = d.const_app(p.inverse_index, &[pp, zero_nat]);
        let concl = d.eq(sigma_zero, zero_nat);
        let stmt = d.arrow(prime_ty, concl);

        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);

        let one_le_pp = nat_prime_pos(d, pp, prime_proof);
        let pos_big_p = one_le_pp;
        let (two_le_ty, clause_ty) = prime_parts(d, pp);
        let two_le = d.and_left(two_le_ty, clause_ty, prime_proof);

        let big_p = d.of_nat(pp);
        let one_i = d.ione();

        let sk = one_nat; // succ(zero), literally `d.num(1)`.
        let a = d.of_nat(sk);
        let pm2 = d.sub(pp, two_nat);
        let pw = d.ipow(a, pm2);

        let pos_sk = d.lemma(p.nat.zero_lt_succ, &[zero_nat]); // 0 < 1
        let ub_sk = two_le; // Lt one_nat pp: `Nat.lt := Nat.le ∘ succ`, `succ one_nat = two_nat`.

        // a = one, via a single delta-unfold of `Int.one := Int.ofNat 1`.
        let a_eq_one = d.irefl(a);

        // a*a = a = one.
        let mul_aa = d.imul(a, a);
        let mul_a_one = d.imul(a, one_i);
        let step1 = d.icongr(a, one_i, a_eq_one, &|d, x| d.imul(a, x));
        let step2 = d.const_app(p.mul_one, &[a]);
        let (_, mul_aa_eq_a) = d.ichain(mul_aa, &[(mul_a_one, step1), (a, step2)]);
        let mul_aa_eq_one = d.itrans(mul_aa, a, one_i, mul_aa_eq_a, a_eq_one);

        // ModEq p (a*a) one, retyped from ModEq.refl at one through mul_aa_eq_one.
        let refl_one_modeq = d.const_app(p.mod_eq_refl, &[big_p, one_i]);
        let mul_aa_eq_one_rev = d.isymm(mul_aa, one_i, mul_aa_eq_one);
        let sq_modeq_one =
            d.int_eq_rewrite(one_i, mul_aa, mul_aa_eq_one_rev, refl_one_modeq, &|d, x| {
                super::modeq::imodeq(d, big_p, x, one_i)
            });

        // ModEq p (a*pw) one.
        let mip = d.const_app(p.mul_inv_of_pow, &[pp, sk, prime_proof, pos_sk, ub_sk]);

        // ModEq p pw a.
        let modeq_pw_a = d.const_app(
            p.mod_eq_inverse_unique,
            &[big_p, a, pw, a, pos_big_p, mip, sq_modeq_one],
        );

        // r := emod(pw, big_p) = a, via canonical residues.
        let a_nonneg = d.lemma(p.nat.zero_le, &[sk]);
        let emod_a_eq = emod_eq_self_of_in_range(d, a, big_p, pos_big_p, a_nonneg, ub_sk);
        let r = d.iemod(pw, big_p);
        let emod_a_raw = d.iemod(a, big_p);
        let (_, r_eq_a) = d.ichain(r, &[(emod_a_raw, modeq_pw_a), (a, emod_a_eq)]);

        // Eq Nat sk (natAbs r), via the natAbs-transparency trick.
        let refl_sk = d.refl(sk);
        let r_eq_a_rev = d.isymm(r, a, r_eq_a);
        let nat_eq = d.int_eq_rewrite(a, r, r_eq_a_rev, refl_sk, &|d, x| {
            let nx = {
                let f = p.nat_abs;
                d.const_app(f, &[x])
            };
            d.eq(sk, nx)
        });

        // sub(natAbs r, one_nat) = sub(sk, one_nat) = sub(one_nat, one_nat) = zero.
        let mag = {
            let f = p.nat_abs;
            d.const_app(f, &[r])
        };
        let sub_congr = d.congr(sk, mag, nat_eq, &|d, x| d.sub(x, one_nat));
        let sub_sk_one = d.sub(sk, one_nat);
        let sub_mag_one = d.sub(mag, one_nat);
        let concrete_zero = d.refl(zero_nat); // retyped as Eq Nat sub_sk_one zero_nat
        let sub_congr_rev = d.symm(sub_sk_one, sub_mag_one, sub_congr);
        let result = d.trans(
            sub_mag_one,
            sub_sk_one,
            zero_nat,
            sub_congr_rev,
            concrete_zero,
        );

        let proof = d.lam_fv(prime_fv, prime_ty, result);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.inverseIndex_fixes_last :
/// ∀ p, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) → Eq Nat (inverseIndex p (p-2)) (p-2)`
///
/// The other direct computation [`declare_inverse_index_fixed_point`]'s doc
/// names but does not build: `p-1 ≡ -1 [p]` is its own modular inverse, i.e.
/// `σ (p-2) = p-2` (`σ := Nat.inverseIndex p`). With `sk := succ(p-2)` (so
/// `sk = p-1`, [`succ_pm2_eq_pm1`]) and `a := ofNat sk`, `pw := a^(p-2)`:
///
/// `a ≡ -1 [p]` — via `a = ofNat(p-1) = p - 1` (the same `Int.sub`-unfolding
/// bridge [`declare_inverse_index_fixed_point`] builds as `sub_eq_pm1`,
/// rebuilt here) composed with [`neg_one_modeq_p_minus_one`] — so `a*a ≡
/// (-1)*(-1) = 1 [p]` (`Int.ModEq.mul` at the same hypothesis twice, then the
/// concrete literal fact `(-1)*(-1) = 1`, the same `rfl` `gcd.rs`'s
/// `neg_neg`'s own `negone_sq_eq_one` fragment relies on). From there the
/// route is identical to [`declare_inverse_index_fixes_zero`]:
/// `Int.modEq_inverse_unique` collapses `a`'s two inverses `pw` and `a` to
/// `ModEq p pw a`; canonical residues force the literal `Eq Int r a`; the
/// `Int.natAbs` transparency trick gives `Eq Nat sk (natAbs r)`; and
/// `sk = p-1` plus `Nat.sub_succ` (twice: `(p-1)-1 = pred(p-1) = p-2`) closes
/// the goal.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_inverse_index_fixes_last(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.inverse_index_fixes_last, 1, &|d, v| {
        let pp = v[0];
        let prime_ty = prime_condition(d, pp);

        let one_nat = d.num(1);
        let two_nat = d.num(2);
        let zero_nat = d.zero();
        let pm1 = d.sub(pp, one_nat);
        let pm2 = d.sub(pp, two_nat);
        let sigma_pm2 = d.const_app(p.inverse_index, &[pp, pm2]);
        let concl = d.eq(sigma_pm2, pm2);
        let stmt = d.arrow(prime_ty, concl);

        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);

        let one_le_pp = nat_prime_pos(d, pp, prime_proof);
        let pos_big_p = one_le_pp;

        let big_p = d.of_nat(pp);
        let one_i = d.ione();
        let neg_one = d.ineg(one_i);

        let sk = d.succ(pm2);
        let a = d.of_nat(sk);
        let pw = d.ipow(a, pm2);

        // sk = pm1.
        let sk_eq_pm1 = succ_pm2_eq_pm1(d, pp, prime_proof);

        // pos_sk, ub_sk.
        let pos_sk = d.lemma(p.nat.zero_lt_succ, &[pm2]);
        let one_pos = d.lemma(p.nat.zero_lt_succ, &[zero_nat]);
        let pm1_lt_pp = d.lemma(p.nat.sub_lt, &[pp, one_nat, one_le_pp, one_pos]);
        let sk_eq_pm1_rev = d.symm(sk, pm1, sk_eq_pm1);
        let ub_sk = d.nat_rewrite(pm1, sk, sk_eq_pm1_rev, pm1_lt_pp, &|d, x| d.lt(x, pp));

        // a = ofNat pm1 = big_p - one_i, so ModEq p neg_one a.
        let ofnat_pm1 = d.of_nat(pm1);
        let a_eq_ofnat_pm1 = d.nat_eq_to_int(sk, pm1, sk_eq_pm1, &|d, y| d.of_nat(y));

        let succ_pm1 = d.succ(pm1);
        let cancel1 = d.lemma(p.nat.sub_add_cancel, &[one_nat, pp, one_le_pp]);
        let key = d.nat_eq_to_int(succ_pm1, pp, cancel1, &|d, y| d.of_nat(y));
        let sum_pm1_one = d.iadd(ofnat_pm1, one_i);
        let cancel_right = d.const_app(p.add_neg_cancel_right, &[ofnat_pm1, one_i]);
        let congr_key = d.icongr(sum_pm1_one, big_p, key, &|d, t| d.iadd(t, neg_one));
        let lhs_after = d.iadd(big_p, neg_one);
        let x_term = d.iadd(sum_pm1_one, neg_one);
        let congr_key_rev = d.isymm(x_term, lhs_after, congr_key);
        let sub_eq_pm1 = d.itrans(lhs_after, x_term, ofnat_pm1, congr_key_rev, cancel_right);
        let p_minus_one = d.isub(big_p, one_i);

        let sub_eq_pm1_rev = d.isymm(lhs_after, ofnat_pm1, sub_eq_pm1);
        let a_eq_p_minus_one = d.itrans(a, ofnat_pm1, p_minus_one, a_eq_ofnat_pm1, sub_eq_pm1_rev);

        let base_modeq = neg_one_modeq_p_minus_one(d, big_p, pos_big_p); // ModEq p neg_one p_minus_one
        let a_eq_p_minus_one_rev = d.isymm(a, p_minus_one, a_eq_p_minus_one);
        let modeq_negone_a =
            d.int_eq_rewrite(p_minus_one, a, a_eq_p_minus_one_rev, base_modeq, &|d, x| {
                super::modeq::imodeq(d, big_p, neg_one, x)
            });

        // ModEq p (a*a) one, via neg_one*neg_one = one and mod_eq_mul.
        let neg_one_sq = d.imul(neg_one, neg_one);
        let neg_one_sq_eq_one = {
            let fwd = d.const_app(p.neg_one_mul, &[neg_one]); // neg_one_sq = neg neg_one
            let neg_neg_one_pf = d.irefl(one_i); // neg (neg one) = one, by rfl
            let neg_neg_one = d.ineg(neg_one);
            d.itrans(neg_one_sq, neg_neg_one, one_i, fwd, neg_neg_one_pf)
        };
        let mul_aa = d.imul(a, a);
        let modeq_negsq_aa = d.const_app(
            p.mod_eq_mul,
            &[
                big_p,
                neg_one,
                a,
                neg_one,
                a,
                pos_big_p,
                modeq_negone_a,
                modeq_negone_a,
            ],
        ); // ModEq p (neg_one*neg_one) (a*a)
        let modeq_one_aa = d.int_eq_rewrite(
            neg_one_sq,
            one_i,
            neg_one_sq_eq_one,
            modeq_negsq_aa,
            &|d, x| super::modeq::imodeq(d, big_p, x, mul_aa),
        );
        let sq_modeq_one = d.const_app(p.mod_eq_symm, &[big_p, one_i, mul_aa, modeq_one_aa]);

        // ModEq p (a*pw) one.
        let mip = d.const_app(p.mul_inv_of_pow, &[pp, sk, prime_proof, pos_sk, ub_sk]);

        // ModEq p pw a.
        let modeq_pw_a = d.const_app(
            p.mod_eq_inverse_unique,
            &[big_p, a, pw, a, pos_big_p, mip, sq_modeq_one],
        );

        // r := emod(pw, big_p) = a.
        let a_nonneg = d.lemma(p.nat.zero_le, &[sk]);
        let emod_a_eq = emod_eq_self_of_in_range(d, a, big_p, pos_big_p, a_nonneg, ub_sk);
        let r = d.iemod(pw, big_p);
        let emod_a_raw = d.iemod(a, big_p);
        let (_, r_eq_a) = d.ichain(r, &[(emod_a_raw, modeq_pw_a), (a, emod_a_eq)]);

        // Eq Nat sk (natAbs r).
        let refl_sk = d.refl(sk);
        let r_eq_a_rev = d.isymm(r, a, r_eq_a);
        let nat_eq = d.int_eq_rewrite(a, r, r_eq_a_rev, refl_sk, &|d, x| {
            let nx = {
                let f = p.nat_abs;
                d.const_app(f, &[x])
            };
            d.eq(sk, nx)
        });
        let mag = {
            let f = p.nat_abs;
            d.const_app(f, &[r])
        };

        // pm1 = mag.
        let sk_eq_pm1_rev2 = d.symm(sk, pm1, sk_eq_pm1);
        let pm1_eq_mag = d.trans(pm1, sk, mag, sk_eq_pm1_rev2, nat_eq);

        // sub(pm1, one_nat) = pm2, via `Nat.sub_succ` twice.
        let sub_succ_1 = d.lemma(p.nat.sub_succ, &[pm1, zero_nat]);
        let sub_pm1_zero = d.sub(pm1, zero_nat);
        let sub_zero_pf = d.lemma(p.nat.sub_zero, &[pm1]);
        let pred_sub_pm1_zero = d.pred(sub_pm1_zero);
        let pred_pm1 = d.pred(pm1);
        let congr_pred = d.congr(sub_pm1_zero, pm1, sub_zero_pf, &|d, x| d.pred(x));
        let sub_pm1_one = d.sub(pm1, one_nat);
        let (_, sub_pm1_one_eq_pred_pm1) = d.chain(
            sub_pm1_one,
            &[(pred_sub_pm1_zero, sub_succ_1), (pred_pm1, congr_pred)],
        );
        let sub_succ_2 = d.lemma(p.nat.sub_succ, &[pp, one_nat]);
        let pred_pm1_eq_pm2 = d.symm(pm2, pred_pm1, sub_succ_2);
        let sub_pm1_one_eq_pm2 = d.trans(
            sub_pm1_one,
            pred_pm1,
            pm2,
            sub_pm1_one_eq_pred_pm1,
            pred_pm1_eq_pm2,
        );

        // sub(mag, one_nat) = pm2, via pm1 = mag.
        let sub_mag_one = d.sub(mag, one_nat);
        let congr_sub = d.congr(pm1, mag, pm1_eq_mag, &|d, x| d.sub(x, one_nat));
        let congr_sub_rev = d.symm(sub_pm1_one, sub_mag_one, congr_sub);
        let result = d.trans(
            sub_mag_one,
            sub_pm1_one,
            pm2,
            congr_sub_rev,
            sub_pm1_one_eq_pm2,
        );

        let proof = d.lam_fv(prime_fv, prime_ty, result);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.inverseIndex_interior_fixed_point_free :
/// ∀ p, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) →
///   ∀ k, Lt zero k → Lt k (p-2) → Not (Eq Nat (inverseIndex p k) k)`
///
/// The immediate contrapositive of [`declare_inverse_index_fixed_point`]: on
/// the interior `{1,…,p-3}` (`0 < k < p-2`, excluding both of `σ`'s exactly
/// two fixed points `0` and `p-2` — [`declare_inverse_index_fixes_zero`] /
/// [`declare_inverse_index_fixes_last`]), `σ := Nat.inverseIndex p` has no
/// fixed point. `k < p-2 < p-1` (`p-2 = pred(p-1)`, via
/// [`succ_pm2_eq_pm1`] rewriting `Nat.lt_succ_self`, weakened to `≤` and
/// chained with `hhi` through `Nat.le_trans` — the same `Lt := Le ∘ succ`
/// retyping [`le_of_lt_local`] already relies on) supplies
/// `inverseIndex_fixed_point`'s own bound hypothesis; its conclusion `k=0 ∨
/// k=p-2` is refuted in both disjuncts directly by `0 < k` / `k < p-2`
/// ([`ne_of_lt_local`]).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_inverse_index_interior_fixed_point_free(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.inverse_index_interior_fixed_point_free, 1, &|d, v| {
        let pp = v[0];
        let prime_ty = prime_condition(d, pp);
        let nat = d.nat_ty();

        let one_nat = d.num(1);
        let two_nat = d.num(2);
        let zero_nat = d.zero();
        let pm1 = d.sub(pp, one_nat);
        let pm2 = d.sub(pp, two_nat);

        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hlo_ty = d.lt(zero_nat, k);
        let hhi_ty = d.lt(k, pm2);
        let sigma_k = d.const_app(p.inverse_index, &[pp, k]);
        let heq_ty = d.eq(sigma_k, k);
        let not_heq_ty = d.not(heq_ty);

        let stmt = {
            let body = d.arrow(hhi_ty, not_heq_ty);
            let with_lo = d.arrow(hlo_ty, body);
            let with_k = d.pi_fv(k_fv, nat, with_lo);
            d.arrow(prime_ty, with_k)
        };

        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);
        let hlo_fv = d.fresh_fvar();
        let hlo = d.kernel().fvar(hlo_fv);
        let hhi_fv = d.fresh_fvar();
        let hhi = d.kernel().fvar(hhi_fv);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        // k < p-2 < p-1: `pm2 < succ pm2 = pm1` (`succ_pm2_eq_pm1`), weakened
        // to `≤` and chained with `hhi` via `Nat.le_trans` (`Lt := Le ∘ succ`
        // retyping throughout, [`le_of_lt_local`]'s own idiom).
        let sk_eq_pm1 = succ_pm2_eq_pm1(d, pp, prime_proof); // Eq Nat (succ pm2) pm1
        let succ_pm2 = d.succ(pm2);
        let pm2_lt_succ_pm2 = d.lemma(p.nat.lt_succ_self, &[pm2]); // Lt pm2 (succ pm2)
        let pm2_lt_pm1 = d.nat_rewrite(succ_pm2, pm1, sk_eq_pm1, pm2_lt_succ_pm2, &|d, x| {
            d.lt(pm2, x)
        });
        let le_pm2_pm1 = le_of_lt_local(d, pm2, pm1, pm2_lt_pm1); // Le pm2 pm1
        let sk_k = d.succ(k);
        let k_lt_pm1 = d.lemma(p.nat.le_trans, &[sk_k, pm2, pm1, hhi, le_pm2_pm1]); // Le sk_k pm1 ~ Lt k pm1

        let disj = d.const_app(
            p.inverse_index_fixed_point,
            &[pp, k, prime_proof, k_lt_pm1, heq],
        );

        let is_zero = d.eq(k, zero_nat);
        let is_pm2 = d.eq(k, pm2);
        let false_ty = d.false_ty();

        let on_left = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
            // h : Eq Nat k zero, contradicts hlo : Lt zero k.
            let h_rev = d.symm(k, zero_nat, h); // Eq Nat zero k
            let ne = ne_of_lt_local(d, zero_nat, k, hlo); // Not (Eq Nat zero k)
            d.apply(ne, &[h_rev])
        };
        let on_right = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
            // h : Eq Nat k pm2, contradicts hhi : Lt k pm2.
            let ne = ne_of_lt_local(d, k, pm2, hhi); // Not (Eq Nat k pm2)
            d.apply(ne, &[h])
        };

        let refute = d.or_elim(is_zero, is_pm2, false_ty, disj, on_left, on_right);

        let inner_body = {
            let with_heq = d.lam_fv(heq_fv, heq_ty, refute);
            let with_hhi = d.lam_fv(hhi_fv, hhi_ty, with_heq);
            let with_lo = d.lam_fv(hlo_fv, hlo_ty, with_hhi);
            d.lam_fv(k_fv, nat, with_lo)
        };
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
// UPDATE, later still 2026-08-24: it WAS built, just below this comment
// (`declare_prod_range_pairing_collapse` and its helpers, `family_stmt`
// through `family_succ_succ_proof`) — the paragraph above describes the state
// BEFORE that induction landed, kept for the record rather than deleted.
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
// `Int.wilson` was NOT declared at this point in the file's history; it now
// is, near the bottom, via the pairing collapse this comment said was
// missing — the sign comes from the two BOUNDARY survivors (`1` and `p-1`),
// not from anything `factorial_sq_modeq_one` computes.
// ============================================================================

/// `ModEq n x (emod x n)`, given `0 < n` — a value is always congruent to its
/// own canonical remainder. `emod x n` is already in `[0, n)`
/// (`emod_nonneg`/`emod_lt_of_pos`), so [`emod_eq_self_of_in_range`] applied
/// to `emod x n` itself gives `emod (emod x n) n = emod x n`; `ModEq n x
/// (emod x n)` unfolds (by `Int.ModEq`'s own definition) to exactly the
/// `Eq Int (emod x n) (emod (emod x n) n)` that is the `symm` of that fact.
pub(super) fn emod_modeq_self(d: &mut IntDev<'_>, x: ExprId, n: ExprId, n_pos: ExprId) -> ExprId {
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

// ============================================================================
// `Int.prod_range_pairing_collapse` — the interior collapse, landed
// 2026-08-24. This is the "collapse lemma" the module doc above (What Wilson
// is blocked on now) describes as unbuilt: given a fixed-point-free
// involution `σ` pairing up `[0,n)`, where every pair's product is `≡ 1
// [bigp]`, the WHOLE product `prodRange F n` is `≡ 1 [bigp]`.
//
// Proved by "two-step" structural induction on `n` — `And (family n) (family
// (succ n))`, both halves proved together by ordinary `Nat.rec` — which needs
// no `WellFounded.fix`: the recursive step always decreases the domain by
// exactly 2, and `family n` is available as the LEFT half of the induction
// hypothesis one step later, at `succ n`.
//
// The step (`family (succ (succ m))`, from `ih_lo : family m`): `σ`'s own
// involution pairs the top index `succ m` with `i0 := σ (succ m)`. If
// `i0 = m` the pair is already at the top: peel both factors via two
// `prodRange_succ` unfoldings and recurse directly (`peel_and_close`, the
// case-independent closing argument). Otherwise (`i0 < m`) conjugate `σ` by
// the transposition `τ := transposition i0 m`
// (`Nat.transposition`/`Nat.conjugate_injective`/`Nat.conjugate_maps_into`,
// `nat_prelude/transposition.rs`): conjugation moves the swap to the top
// (`σ' m = succ m`, `σ' (succ m) = m`) and — because `τ` is its own inverse —
// PRESERVES fixed-point-freeness and involution, and composed with `F` it
// preserves the pairwise congruence at the conjugated index; this lands back
// in the direct case with `G := F ∘ τ` and `σ'` in place of `F` and `σ`, and
// `peel_and_close` finishes it the same way.
// ============================================================================

// --- small order helpers, local to this section ----------------------------

/// `h : Lt a b ⊢ Le a b`.
fn le_of_lt_local(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let sa = d.succ(a);
    let le_a_sa = d.lemma(p.nat.le_succ, &[a]);
    d.lemma(p.nat.le_trans, &[a, sa, b, le_a_sa, h])
}

/// `h : Lt a b ⊢ Not (Eq Nat a b)`.
fn ne_of_lt_local(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);
    let eq_ty = d.eq(a, b);
    let motive = d.eq_motive(a, &|d, x| d.lt(x, b));
    let transported = d.transport(a, motive, h, b, heq); // Lt b b
    let refuted = d.lemma(p.nat.not_succ_le_self, &[b]); // Not (Le (succ b) b)
    let false_pf = d.apply(refuted, &[transported]);
    d.lam_fv(heq_fv, eq_ty, false_pf)
}

/// `hle : Le x y`, `hne : Not (Eq Nat x y) ⊢ Lt x y`.
fn lt_of_le_ne(d: &mut IntDev<'_>, x: ExprId, y: ExprId, hle: ExprId, hne: ExprId) -> ExprId {
    let p = d.int();
    let case = d.lemma(p.nat.lt_or_eq_of_le, &[x, y, hle]);
    let lt_ty = d.lt(x, y);
    let eq_ty = d.eq(x, y);
    d.or_elim(lt_ty, eq_ty, lt_ty, case, &|_d, h| h, &move |d, h| {
        let f = d.apply(hne, &[h]);
        d.absurd(lt_ty, f)
    })
}

/// `hkm : Lt k m ⊢ Lt k (succ (succ m))`.
fn lt_below_n2(d: &mut IntDev<'_>, k: ExprId, m: ExprId, hkm: ExprId) -> ExprId {
    let p = d.int();
    let sm = d.succ(m);
    let n2 = d.succ(sm);
    let le_m_sm = d.lemma(p.nat.le_succ, &[m]);
    let le_sm_n2 = d.lemma(p.nat.le_succ, &[sm]);
    let le_m_n2 = d.lemma(p.nat.le_trans, &[m, sm, n2, le_m_sm, le_sm_n2]);
    d.lemma(p.nat.lt_of_lt_of_le, &[k, m, n2, hkm, le_m_n2])
}

/// `hx_lt_n2 : Lt x (succ (succ m))`, `hx_ne_m : Not (Eq Nat x m)`,
/// `hx_ne_sm : Not (Eq Nat x (succ m)) ⊢ Lt x m`.
fn closure_lt_m(
    d: &mut IntDev<'_>,
    x: ExprId,
    m: ExprId,
    hx_lt_n2: ExprId,
    hx_ne_m: ExprId,
    hx_ne_sm: ExprId,
) -> ExprId {
    let p = d.int();
    let sm = d.succ(m);
    let le_x_sm = d.lemma(p.nat.le_of_lt_succ, &[x, sm, hx_lt_n2]);
    let lt_x_sm = lt_of_le_ne(d, x, sm, le_x_sm, hx_ne_sm);
    let le_x_m = d.lemma(p.nat.le_of_lt_succ, &[x, m, lt_x_sm]);
    lt_of_le_ne(d, x, m, le_x_m, hx_ne_m)
}

/// `heq : Eq Nat (sigma k) target`, `target_eq_sigma_w : Eq Nat (sigma w) target`,
/// `hk_n2 : Lt k n2`, `hw_n2 : Lt w n2`, `k_lt_w : Lt k w` ⊢ `False` —
/// `sigma k = sigma w` (both equal `target`) forces `k = w` by injectivity,
/// contradicting `k < w`.
#[allow(clippy::too_many_arguments)]
fn contradiction_via_injectivity(
    d: &mut IntDev<'_>,
    sigma: ExprId,
    inj: ExprId,
    k: ExprId,
    w: ExprId,
    target: ExprId,
    heq: ExprId,
    target_eq_sigma_w: ExprId,
    hk_n2: ExprId,
    hw_n2: ExprId,
    k_lt_w: ExprId,
) -> ExprId {
    let sw = d.apply(sigma, &[w]);
    let target_eq_sw_rev = d.symm(sw, target, target_eq_sigma_w);
    let sk = d.apply(sigma, &[k]);
    let sk_eq_sw = d.trans(sk, target, sw, heq, target_eq_sw_rev);
    let k_eq_w = d.apply(inj, &[k, w, hk_n2, hw_n2, sk_eq_sw]);
    let k_ne_w = ne_of_lt_local(d, k, w, k_lt_w);
    d.apply(k_ne_w, &[k_eq_w])
}

// --- statement builders ------------------------------------------------------

/// `Nat → Int`.
fn nat_to_int_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    d.arrow(nat, int_ty)
}

/// `Nat → Nat`.
fn nat_to_nat_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    d.arrow(nat, nat)
}

/// `∀ k, Lt k bound → prop(k)`.
fn forall_below(
    d: &mut IntDev<'_>,
    bound: ExprId,
    prop: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hk_ty = d.lt(k, bound);
    let body = prop(d, k);
    let arrowed = d.arrow(hk_ty, body);
    d.pi_fv(k_fv, nat, arrowed)
}

/// `∀ k, Lt k m → Not (Eq Nat (sigma k) k)`.
fn fpf_ty(d: &mut IntDev<'_>, sigma: ExprId, m: ExprId) -> ExprId {
    forall_below(d, m, &|d, k| {
        let sk = d.apply(sigma, &[k]);
        let eq_ = d.eq(sk, k);
        d.not(eq_)
    })
}

/// `∀ k, Lt k m → Eq Nat (sigma (sigma k)) k`.
fn invol_ty(d: &mut IntDev<'_>, sigma: ExprId, m: ExprId) -> ExprId {
    forall_below(d, m, &|d, k| {
        let sk = d.apply(sigma, &[k]);
        let ssk = d.apply(sigma, &[sk]);
        d.eq(ssk, k)
    })
}

/// `∀ k, Lt k m → ModEq bigp (mul (f k) (f (sigma k))) one`.
fn pairwise_ty(d: &mut IntDev<'_>, bigp: ExprId, f: ExprId, sigma: ExprId, m: ExprId) -> ExprId {
    forall_below(d, m, &|d, k| {
        let fk = d.apply(f, &[k]);
        let sk = d.apply(sigma, &[k]);
        let fsk = d.apply(f, &[sk]);
        let prod = d.imul(fk, fsk);
        let one_i = d.ione();
        super::modeq::imodeq(d, bigp, prod, one_i)
    })
}

/// `family(m) : ∀ F σ, InjectiveOn σ m → MapsInto σ m → (fpf) → (invol) →
/// (pairwise) → ModEq bigp (prodRange F m) one`.
fn family_stmt(d: &mut IntDev<'_>, bigp: ExprId, m: ExprId) -> ExprId {
    let p = d.int();
    let fn_int_ty = nat_to_int_ty(d);
    let fn_nat_ty = nat_to_nat_ty(d);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let sigma_fv = d.fresh_fvar();
    let sigma = d.kernel().fvar(sigma_fv);

    let inj_ty = d.const_app(p.nat.injective_on, &[sigma, m]);
    let maps_ty = d.const_app(p.nat.maps_into, &[sigma, m]);
    let fpf = fpf_ty(d, sigma, m);
    let invol = invol_ty(d, sigma, m);
    let pairwise = pairwise_ty(d, bigp, f, sigma, m);

    let concl = {
        let pr = d.const_app(p.prod_range, &[f, m]);
        let one_i = d.ione();
        super::modeq::imodeq(d, bigp, pr, one_i)
    };

    let after_hyps = {
        let w1 = d.arrow(pairwise, concl);
        let w2 = d.arrow(invol, w1);
        let w3 = d.arrow(fpf, w2);
        let w4 = d.arrow(maps_ty, w3);
        d.arrow(inj_ty, w4)
    };
    let with_sigma = d.pi_fv(sigma_fv, fn_nat_ty, after_hyps);
    d.pi_fv(f_fv, fn_int_ty, with_sigma)
}

/// `And (family m) (family (succ m))`.
fn strengthened_stmt(d: &mut IntDev<'_>, bigp: ExprId, m: ExprId) -> ExprId {
    let fam_m = family_stmt(d, bigp, m);
    let sm = d.succ(m);
    let fam_sm = family_stmt(d, bigp, sm);
    d.and(fam_m, fam_sm)
}

// --- base case: family(0), family(1) ----------------------------------------

/// `family(0)` — vacuous: `prodRange F zero` is defeq `one`, so
/// `ModEq.refl` closes it directly.
fn family_zero_proof(d: &mut IntDev<'_>, bigp: ExprId) -> ExprId {
    let p = d.int();
    let fn_int_ty = nat_to_int_ty(d);
    let fn_nat_ty = nat_to_nat_ty(d);
    let zero = d.zero();

    let f_fv = d.fresh_fvar();
    let sigma_fv = d.fresh_fvar();
    let sigma = d.kernel().fvar(sigma_fv);
    let inj_ty = d.const_app(p.nat.injective_on, &[sigma, zero]);
    let maps_ty = d.const_app(p.nat.maps_into, &[sigma, zero]);
    let fpf = fpf_ty(d, sigma, zero);
    let invol = invol_ty(d, sigma, zero);
    let pairwise = {
        let f = d.kernel().fvar(f_fv);
        pairwise_ty(d, bigp, f, sigma, zero)
    };

    let inj_fv = d.fresh_fvar();
    let maps_fv = d.fresh_fvar();
    let fpf_fv = d.fresh_fvar();
    let invol_fv = d.fresh_fvar();
    let pairwise_fv = d.fresh_fvar();

    let one_i = d.ione();
    let body = d.const_app(p.mod_eq_refl, &[bigp, one_i]);

    let with_pairwise = d.lam_fv(pairwise_fv, pairwise, body);
    let with_invol = d.lam_fv(invol_fv, invol, with_pairwise);
    let with_fpf = d.lam_fv(fpf_fv, fpf, with_invol);
    let with_maps = d.lam_fv(maps_fv, maps_ty, with_fpf);
    let with_inj = d.lam_fv(inj_fv, inj_ty, with_maps);
    let with_sigma = d.lam_fv(sigma_fv, fn_nat_ty, with_inj);
    d.lam_fv(f_fv, fn_int_ty, with_sigma)
}

/// `family(1)` — vacuous by contradiction: `MapsInto σ 1` forces `σ 0 = 0`,
/// contradicting the fixed-point-free hypothesis at `0`.
fn family_one_proof(d: &mut IntDev<'_>, bigp: ExprId) -> ExprId {
    let p = d.int();
    let fn_int_ty = nat_to_int_ty(d);
    let fn_nat_ty = nat_to_nat_ty(d);
    let zero = d.zero();
    let one_n = d.succ(zero);

    let f_fv = d.fresh_fvar();
    let sigma_fv = d.fresh_fvar();
    let sigma = d.kernel().fvar(sigma_fv);
    let inj_ty = d.const_app(p.nat.injective_on, &[sigma, one_n]);
    let maps_ty = d.const_app(p.nat.maps_into, &[sigma, one_n]);
    let fpf = fpf_ty(d, sigma, one_n);
    let invol = invol_ty(d, sigma, one_n);
    let pairwise = {
        let f = d.kernel().fvar(f_fv);
        pairwise_ty(d, bigp, f, sigma, one_n)
    };

    let inj_fv = d.fresh_fvar();
    let maps_fv = d.fresh_fvar();
    let maps = d.kernel().fvar(maps_fv);
    let fpf_fv = d.fresh_fvar();
    let fpf_p = d.kernel().fvar(fpf_fv);
    let invol_fv = d.fresh_fvar();
    let pairwise_fv = d.fresh_fvar();

    let sigma_0 = d.apply(sigma, &[zero]);
    let hz = d.lemma(p.nat.zero_lt_succ, &[zero]); // Lt zero one_n
    let s0_lt_1 = d.apply(maps, &[zero, hz]); // Lt sigma_0 one_n
    let le_s0_0 = d.lemma(p.nat.le_of_lt_succ, &[sigma_0, zero, s0_lt_1]); // Le sigma_0 zero
    let zero_le_s0 = d.lemma(p.nat.zero_le, &[sigma_0]); // Le zero sigma_0
    let s0_eq_0 = d.lemma(p.nat.le_antisymm, &[sigma_0, zero, le_s0_0, zero_le_s0]);
    let fpf_at_0 = d.apply(fpf_p, &[zero, hz]); // Not (Eq Nat sigma_0 zero)
    let false_pf = d.apply(fpf_at_0, &[s0_eq_0]);

    let concl = {
        let f = d.kernel().fvar(f_fv);
        let pr = d.const_app(p.prod_range, &[f, one_n]);
        let one_i = d.ione();
        super::modeq::imodeq(d, bigp, pr, one_i)
    };
    let body = d.absurd(concl, false_pf);

    let with_pairwise = d.lam_fv(pairwise_fv, pairwise, body);
    let with_invol = d.lam_fv(invol_fv, invol, with_pairwise);
    let with_fpf = d.lam_fv(fpf_fv, fpf, with_invol);
    let with_maps = d.lam_fv(maps_fv, maps_ty, with_fpf);
    let with_inj = d.lam_fv(inj_fv, inj_ty, with_maps);
    let with_sigma = d.lam_fv(sigma_fv, fn_nat_ty, with_inj);
    d.lam_fv(f_fv, fn_int_ty, with_sigma)
}

// --- the closing argument, shared by both branches of the step case --------

/// Given `f`, `sigma` on domain `n2 = succ (succ m)`, the boundary facts
/// `sigma m = succ m` / `sigma (succ m) = m`, the full-domain hypotheses, and
/// `ih_lo : family(m)`, produce a proof of `ModEq bigp (prodRange f n2) one`.
#[allow(clippy::too_many_arguments)]
fn peel_and_close(
    d: &mut IntDev<'_>,
    bigp: ExprId,
    pos_bigp: ExprId,
    m: ExprId,
    f: ExprId,
    sigma: ExprId,
    inj: ExprId,
    maps: ExprId,
    fpf_p: ExprId,
    invol_p: ExprId,
    pairwise_p: ExprId,
    sigma_m_eq_sm: ExprId,
    sigma_sm_eq_m: ExprId,
    ih_lo: ExprId,
) -> ExprId {
    let p = d.int();
    let nat = d.nat_ty();
    let sm = d.succ(m);
    let n2 = d.succ(sm);
    let m_lt_sm = d.lemma(p.nat.lt_succ_self, &[m]);
    let sm_lt_n2 = d.lemma(p.nat.lt_succ_self, &[sm]);
    let le_m_sm = le_of_lt_local(d, m, sm, m_lt_sm);
    let le_sm_n2 = le_of_lt_local(d, sm, n2, sm_lt_n2);
    let m_lt_n2 = d.lemma(p.nat.lt_of_lt_of_le, &[m, sm, n2, m_lt_sm, le_sm_n2]);

    // --- InjectiveOn sigma m : trivial weakening. ---
    let inj_m = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let ha_fv = d.fresh_fvar();
        let ha = d.kernel().fvar(ha_fv);
        let ha_ty = d.lt(a, m);
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);
        let hb_ty = d.lt(b, m);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let sa = d.apply(sigma, &[a]);
        let sb = d.apply(sigma, &[b]);
        let heq_ty = d.eq(sa, sb);

        let ha_n2 = lt_below_n2(d, a, m, ha);
        let hb_n2 = lt_below_n2(d, b, m, hb);
        let result = d.apply(inj, &[a, b, ha_n2, hb_n2, heq]);

        // `InjectiveOn`'s Pi structure is `a -> b -> Lt a n -> Lt b n -> Eq
        // (sigma a)(sigma b) -> Eq a b` (both values before both proofs, per
        // `nat_prelude/restrict_pair.rs`'s `declare_restrict_pair_injective`),
        // so the binders here must nest in that same order.
        let with_heq = d.lam_fv(heq_fv, heq_ty, result);
        let with_hb = d.lam_fv(hb_fv, hb_ty, with_heq);
        let with_ha = d.lam_fv(ha_fv, ha_ty, with_hb);
        let with_b = d.lam_fv(b_fv, nat, with_ha);
        d.lam_fv(a_fv, nat, with_b)
    };

    // --- MapsInto sigma m : needs the closure argument. ---
    let maps_m = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let hk_ty = d.lt(k, m);

        let hk_n2 = lt_below_n2(d, k, m, hk);
        let sk = d.apply(sigma, &[k]);
        let sk_lt_n2 = d.apply(maps, &[k, hk_n2]);

        let sk_ne_m = {
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);
            let eq_ty = d.eq(sk, m);
            let k_lt_sm = d.lemma(p.nat.lt_of_lt_of_le, &[k, m, sm, hk, le_m_sm]);
            let false_pf = contradiction_via_injectivity(
                d,
                sigma,
                inj,
                k,
                sm,
                m,
                heq,
                sigma_sm_eq_m,
                hk_n2,
                sm_lt_n2,
                k_lt_sm,
            );
            d.lam_fv(heq_fv, eq_ty, false_pf)
        };
        let sk_ne_sm = {
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);
            let eq_ty = d.eq(sk, sm);
            let false_pf = contradiction_via_injectivity(
                d,
                sigma,
                inj,
                k,
                m,
                sm,
                heq,
                sigma_m_eq_sm,
                hk_n2,
                m_lt_n2,
                hk,
            );
            d.lam_fv(heq_fv, eq_ty, false_pf)
        };
        let result = closure_lt_m(d, sk, m, sk_lt_n2, sk_ne_m, sk_ne_sm);

        let with_hk = d.lam_fv(hk_fv, hk_ty, result);
        d.lam_fv(k_fv, nat, with_hk)
    };

    // --- fpf/pairwise on domain m : trivial weakening. ---
    let fpf_m = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let hk_ty = d.lt(k, m);
        let hk_n2 = lt_below_n2(d, k, m, hk);
        let result = d.apply(fpf_p, &[k, hk_n2]);
        let with_hk = d.lam_fv(hk_fv, hk_ty, result);
        d.lam_fv(k_fv, nat, with_hk)
    };
    let invol_m = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let hk_ty = d.lt(k, m);
        let hk_n2 = lt_below_n2(d, k, m, hk);
        let result = d.apply(invol_p, &[k, hk_n2]);
        let with_hk = d.lam_fv(hk_fv, hk_ty, result);
        d.lam_fv(k_fv, nat, with_hk)
    };
    let pairwise_m = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let hk_ty = d.lt(k, m);
        let hk_n2 = lt_below_n2(d, k, m, hk);
        let result = d.apply(pairwise_p, &[k, hk_n2]);
        let with_hk = d.lam_fv(hk_fv, hk_ty, result);
        d.lam_fv(k_fv, nat, with_hk)
    };

    // --- apply the recursive hypothesis. ---
    let ih_applied = d.apply(
        ih_lo,
        &[f, sigma, inj_m, maps_m, fpf_m, invol_m, pairwise_m],
    );
    // ih_applied : ModEq bigp (prodRange f m) one

    // --- pairwise at m : ModEq bigp (f m * f (sigma m)) one, rewritten
    // through sigma_m_eq_sm to ModEq bigp (f m * f (succ m)) one. ---
    let pairwise_at_m = d.apply(pairwise_p, &[m, m_lt_n2]);
    let f_m = d.apply(f, &[m]);
    let sigma_m = d.apply(sigma, &[m]);
    let f_sigma_m = d.apply(f, &[sigma_m]);
    let f_sm = d.apply(f, &[sm]);
    let f_sigma_m_eq_f_sm = d.nat_eq_to_int(sigma_m, sm, sigma_m_eq_sm, &|d, x| d.apply(f, &[x]));
    let boundary_pairwise = d.int_eq_rewrite(
        f_sigma_m,
        f_sm,
        f_sigma_m_eq_f_sm,
        pairwise_at_m,
        &|d, x| {
            let pr = d.imul(f_m, x);
            let one_i = d.ione();
            super::modeq::imodeq(d, bigp, pr, one_i)
        },
    );
    // boundary_pairwise : ModEq bigp (f m * f (succ m)) one

    // --- combine via ModEq.mul, then reassociate to the peeled shape. ---
    let one_i = d.ione();
    let prod_range_m = d.const_app(p.prod_range, &[f, m]);
    let fm_fsm = {
        let fm2 = d.apply(f, &[m]);
        let fsm2 = d.apply(f, &[sm]);
        d.imul(fm2, fsm2)
    };
    let combined = d.const_app(
        p.mod_eq_mul,
        &[
            bigp,
            prod_range_m,
            one_i,
            fm_fsm,
            one_i,
            pos_bigp,
            ih_applied,
            boundary_pairwise,
        ],
    );
    // combined : ModEq bigp (prodRange f m * (f m * f sm)) (one * one)

    let lhs_start = {
        let fm2 = d.apply(f, &[m]);
        let fsm2 = d.apply(f, &[sm]);
        let inner = d.imul(fm2, fsm2);
        d.imul(prod_range_m, inner)
    };
    // `target_lhs := (prodRange f m * f m) * f sm`, defeq `prodRange f n2`
    // via two `prodRange_succ` unfoldings — built to match `mul_assoc`'s own
    // LHS exactly, so `mul_assoc_pf` below applies without any further
    // rewriting.
    let target_lhs = {
        let fm2 = d.apply(f, &[m]);
        let fsm2 = d.apply(f, &[sm]);
        let inner = d.imul(prod_range_m, fm2);
        d.imul(inner, fsm2)
    };
    let mul_assoc_pf = {
        let fm2 = d.apply(f, &[m]);
        let fsm2 = d.apply(f, &[sm]);
        d.const_app(p.mul_assoc, &[prod_range_m, fm2, fsm2])
    };
    // mul_assoc_pf : Eq Int ((prodRange f m * f m) * f sm) (prodRange f m * (f m * f sm))
    let mul_assoc_rev = d.isymm(target_lhs, lhs_start, mul_assoc_pf);
    let combined_reassoc =
        d.int_eq_rewrite(lhs_start, target_lhs, mul_assoc_rev, combined, &|d, x| {
            let rhs = d.imul(one_i, one_i);
            super::modeq::imodeq(d, bigp, x, rhs)
        });
    // combined_reassoc : ModEq bigp (prodRange f n2) (one * one)

    let one_mul_one = d.const_app(p.mul_one, &[one_i]);
    let rhs_pre = d.imul(one_i, one_i);
    d.int_eq_rewrite(rhs_pre, one_i, one_mul_one, combined_reassoc, &|d, x| {
        let pr_n2 = d.const_app(p.prod_range, &[f, n2]);
        super::modeq::imodeq(d, bigp, pr_n2, x)
    })
}

// --- CASE A: `i0 = m` — the pair is already at the top. ---------------------

#[allow(clippy::too_many_arguments)]
fn case_a_body(
    d: &mut IntDev<'_>,
    bigp: ExprId,
    pos_bigp: ExprId,
    m: ExprId,
    f: ExprId,
    sigma: ExprId,
    inj: ExprId,
    maps: ExprId,
    fpf_p: ExprId,
    invol_p: ExprId,
    pairwise_p: ExprId,
    sigma_i0_eq_sm: ExprId, // Eq Nat (sigma i0) sm
    i0: ExprId,             // literally `sigma sm`
    h_i0_eq_m: ExprId,      // Eq Nat i0 m
    ih_lo: ExprId,
) -> ExprId {
    let sm = d.succ(m);
    // `i0` IS `sigma sm` syntactically, so `h_i0_eq_m` already has type
    // `Eq Nat (sigma sm) m`.
    let sigma_sm_eq_m = h_i0_eq_m;
    let sigma_m_eq_sm = {
        let motive = d.eq_motive(i0, &|d, x| {
            let sx = d.apply(sigma, &[x]);
            d.eq(sx, sm)
        });
        d.transport(i0, motive, sigma_i0_eq_sm, m, h_i0_eq_m)
    };
    peel_and_close(
        d,
        bigp,
        pos_bigp,
        m,
        f,
        sigma,
        inj,
        maps,
        fpf_p,
        invol_p,
        pairwise_p,
        sigma_m_eq_sm,
        sigma_sm_eq_m,
        ih_lo,
    )
}

// --- CASE B: `i0 < m` — conjugate by a two-point swap. ----------------------
//
// A Nat-valued two-point swap `tau_raw i j k`, built and proved exactly the
// way `nat_prelude/transposition.rs`'s `Nat.transposition` is (that file's
// own helpers are typed concretely over `NatDev`, so are not reusable here
// without a signature change to a file another lane may be editing; this is
// a self-contained `IntDev` copy, using the same four-`Nat.ble`-cut
// construction). `int_prelude/prod.rs`'s `point_swap` (the `Int`-valued
// analogue used by `Int.prodRange_swap`) and its order-trichotomy helpers
// are reused directly (exposed `pub(super)` in this same module tree).

fn select_nat_true(d: &mut IntDev<'_>, cond: ExprId, a: ExprId, b: ExprId, heq: ExprId) -> ExprId {
    let true_val = d.bool_true();
    let symm_hb = d.bool_symm(cond, true_val, heq);
    let motive = d.bool_eq_motive(true_val, &|d, value| {
        let sel = d.bool_select_nat(value, a, b);
        d.eq(sel, a)
    });
    let refl_case = d.refl(a);
    d.bool_transport(true_val, motive, refl_case, cond, symm_hb)
}

fn select_nat_false(d: &mut IntDev<'_>, cond: ExprId, a: ExprId, b: ExprId, heq: ExprId) -> ExprId {
    let false_val = d.bool_false();
    let symm_hb = d.bool_symm(cond, false_val, heq);
    let motive = d.bool_eq_motive(false_val, &|d, value| {
        let sel = d.bool_select_nat(value, a, b);
        d.eq(sel, b)
    });
    let refl_case = d.refl(b);
    d.bool_transport(false_val, motive, refl_case, cond, symm_hb)
}

fn tau_level4(d: &mut IntDev<'_>, i: ExprId, j: ExprId, k: ExprId) -> ExprId {
    let le_k_j = d.ble(k, j);
    d.bool_select_nat(le_k_j, i, k)
}
fn tau_level3(d: &mut IntDev<'_>, i: ExprId, j: ExprId, k: ExprId) -> ExprId {
    let level4 = tau_level4(d, i, j, k);
    let sk = d.succ(k);
    let lt_k_j = d.ble(sk, j);
    d.bool_select_nat(lt_k_j, k, level4)
}
fn tau_level2(d: &mut IntDev<'_>, i: ExprId, j: ExprId, k: ExprId) -> ExprId {
    let level3 = tau_level3(d, i, j, k);
    let le_k_i = d.ble(k, i);
    d.bool_select_nat(le_k_i, j, level3)
}
fn tau_raw(d: &mut IntDev<'_>, i: ExprId, j: ExprId, k: ExprId) -> ExprId {
    let level2 = tau_level2(d, i, j, k);
    let sk = d.succ(k);
    let lt_k_i = d.ble(sk, i);
    d.bool_select_nat(lt_k_i, k, level2)
}

/// `h : Lt k i ⊢ Eq Nat (tau_raw i j k) k`.
fn tau_eq_lt_i(d: &mut IntDev<'_>, i: ExprId, j: ExprId, k: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let level2 = tau_level2(d, i, j, k);
    let sk = d.succ(k);
    let lt_k_i = d.ble(sk, i);
    let lt_true = d.lemma(p.nat.ble_eq_true_of_le, &[sk, i, h]);
    select_nat_true(d, lt_k_i, k, level2, lt_true)
}

/// `Eq Nat (tau_raw i j i) j`.
fn tau_eq_at_i(d: &mut IntDev<'_>, i: ExprId, j: ExprId) -> ExprId {
    let p = d.int();
    let level2 = tau_level2(d, i, j, i);
    let level3 = tau_level3(d, i, j, i);
    let si = d.succ(i);
    let lt_i_i = d.ble(si, i);
    let lt_succ_self_i = d.lemma(p.nat.lt_succ_self, &[i]);
    let lt_false = super::prod::ble_eq_false_of_lt(d, si, i, lt_succ_self_i);
    let step1 = select_nat_false(d, lt_i_i, i, level2, lt_false);
    let le_i_i = d.ble(i, i);
    let le_refl_i = d.lemma(p.nat.le_refl, &[i]);
    let le_true = d.lemma(p.nat.ble_eq_true_of_le, &[i, i, le_refl_i]);
    let step2 = select_nat_true(d, le_i_i, j, level3, le_true);
    let start = tau_raw(d, i, j, i);
    let (_, proof) = d.chain(start, &[(level2, step1), (j, step2)]);
    proof
}

/// `h1 : Lt i k, h2 : Lt k j ⊢ Eq Nat (tau_raw i j k) k`.
fn tau_eq_between(
    d: &mut IntDev<'_>,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let p = d.int();
    let level2 = tau_level2(d, i, j, k);
    let level3 = tau_level3(d, i, j, k);
    let level4 = tau_level4(d, i, j, k);
    let sk = d.succ(k);

    let le_succ_k = d.lemma(p.nat.le_succ, &[k]);
    let lt_i_sk = d.lemma(p.nat.lt_of_lt_of_le, &[i, k, sk, h1, le_succ_k]);
    let lt_k_i = d.ble(sk, i);
    let lt_k_i_false = super::prod::ble_eq_false_of_lt(d, sk, i, lt_i_sk);
    let step1 = select_nat_false(d, lt_k_i, k, level2, lt_k_i_false);

    let le_k_i = d.ble(k, i);
    let le_k_i_false = super::prod::ble_eq_false_of_lt(d, k, i, h1);
    let step2 = select_nat_false(d, le_k_i, j, level3, le_k_i_false);

    let lt_k_j = d.ble(sk, j);
    let lt_k_j_true = d.lemma(p.nat.ble_eq_true_of_le, &[sk, j, h2]);
    let step3 = select_nat_true(d, lt_k_j, k, level4, lt_k_j_true);

    let start = tau_raw(d, i, j, k);
    let (_, proof) = d.chain(start, &[(level2, step1), (level3, step2), (k, step3)]);
    proof
}

/// `h_ij : Lt i j ⊢ Eq Nat (tau_raw i j j) i`.
fn tau_eq_at_j(d: &mut IntDev<'_>, i: ExprId, j: ExprId, h_ij: ExprId) -> ExprId {
    let p = d.int();
    let level2 = tau_level2(d, i, j, j);
    let level3 = tau_level3(d, i, j, j);
    let level4 = tau_level4(d, i, j, j);
    let sj = d.succ(j);

    let le_succ_j = d.lemma(p.nat.le_succ, &[j]);
    let lt_i_sj = d.lemma(p.nat.lt_of_lt_of_le, &[i, j, sj, h_ij, le_succ_j]);
    let lt_j_i = d.ble(sj, i);
    let lt_j_i_false = super::prod::ble_eq_false_of_lt(d, sj, i, lt_i_sj);
    let step1 = select_nat_false(d, lt_j_i, j, level2, lt_j_i_false);

    let le_j_i = d.ble(j, i);
    let le_j_i_false = super::prod::ble_eq_false_of_lt(d, j, i, h_ij);
    let step2 = select_nat_false(d, le_j_i, j, level3, le_j_i_false);

    let lt_succ_self_j = d.lemma(p.nat.lt_succ_self, &[j]);
    let lt_j_j = d.ble(sj, j);
    let lt_j_j_false = super::prod::ble_eq_false_of_lt(d, sj, j, lt_succ_self_j);
    let step3 = select_nat_false(d, lt_j_j, j, level4, lt_j_j_false);

    let le_refl_j = d.lemma(p.nat.le_refl, &[j]);
    let le_j_j = d.ble(j, j);
    let le_j_j_true = d.lemma(p.nat.ble_eq_true_of_le, &[j, j, le_refl_j]);
    let step4 = select_nat_true(d, le_j_j, i, j, le_j_j_true);

    let start = tau_raw(d, i, j, j);
    let (_, proof) = d.chain(
        start,
        &[
            (level2, step1),
            (level3, step2),
            (level4, step3),
            (i, step4),
        ],
    );
    proof
}

/// `h_ij : Lt i j, h : Lt j k ⊢ Eq Nat (tau_raw i j k) k`.
#[allow(clippy::too_many_arguments)]
fn tau_eq_gt_j(
    d: &mut IntDev<'_>,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    h_ij: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let level2 = tau_level2(d, i, j, k);
    let level3 = tau_level3(d, i, j, k);
    let level4 = tau_level4(d, i, j, k);
    let sk = d.succ(k);

    let le_i_j = le_of_lt_local(d, i, j, h_ij);
    let lt_i_k = d.lemma(p.nat.lt_of_le_of_lt, &[i, j, k, le_i_j, h]);

    let le_succ_k = d.lemma(p.nat.le_succ, &[k]);
    let lt_i_sk = d.lemma(p.nat.lt_of_lt_of_le, &[i, k, sk, lt_i_k, le_succ_k]);
    let lt_k_i = d.ble(sk, i);
    let lt_k_i_false = super::prod::ble_eq_false_of_lt(d, sk, i, lt_i_sk);
    let step1 = select_nat_false(d, lt_k_i, k, level2, lt_k_i_false);

    let le_k_i = d.ble(k, i);
    let le_k_i_false = super::prod::ble_eq_false_of_lt(d, k, i, lt_i_k);
    let step2 = select_nat_false(d, le_k_i, j, level3, le_k_i_false);

    let lt_j_sk = d.lemma(p.nat.lt_of_lt_of_le, &[j, k, sk, h, le_succ_k]);
    let lt_k_j = d.ble(sk, j);
    let lt_k_j_false = super::prod::ble_eq_false_of_lt(d, sk, j, lt_j_sk);
    let step3 = select_nat_false(d, lt_k_j, k, level4, lt_k_j_false);

    let le_k_j = d.ble(k, j);
    let le_k_j_false = super::prod::ble_eq_false_of_lt(d, k, j, h);
    let step4 = select_nat_false(d, le_k_j, i, k, le_k_j_false);

    let start = tau_raw(d, i, j, k);
    let (_, proof) = d.chain(
        start,
        &[
            (level2, step1),
            (level3, step2),
            (level4, step3),
            (k, step4),
        ],
    );
    proof
}

fn tau_close_involutive(
    d: &mut IntDev<'_>,
    i: ExprId,
    j: ExprId,
    x: ExprId,
    y: ExprId,
    z: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let tx = tau_raw(d, i, j, x);
    let ty = tau_raw(d, i, j, y);
    let ttx = tau_raw(d, i, j, tx);
    let congr_step = d.congr(tx, y, h1, &|d, w| tau_raw(d, i, j, w));
    d.trans(ttx, ty, z, congr_step, h2)
}

fn tau_transport_involutive(
    d: &mut IntDev<'_>,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    c: ExprId,
    h: ExprId,
    at_c: ExprId,
) -> ExprId {
    let h_rev = d.symm(k, c, h);
    let motive = d.eq_motive(c, &|d, x| {
        let tx = tau_raw(d, i, j, x);
        let ttx = tau_raw(d, i, j, tx);
        d.eq(ttx, x)
    });
    d.transport(c, motive, at_c, k, h_rev)
}

/// `h_ij : Lt i j ⊢ ∀ k, Eq Nat (tau_raw i j (tau_raw i j k)) k` — `tau_raw`
/// is its own inverse, unconditionally in `k` (mirrors
/// `nat_prelude/transposition.rs`'s `declare_transposition_involutive`).
#[allow(clippy::too_many_lines)]
fn tau_involutive_forall(d: &mut IntDev<'_>, i: ExprId, j: ExprId, h_ij: ExprId) -> ExprId {
    let p = d.int();
    let nat = d.nat_ty();

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let tk = tau_raw(d, i, j, k);
    let ttk = tau_raw(d, i, j, tk);
    let goal = d.eq(ttk, k);

    let lt_k_i = d.lt(k, i);
    let eq_k_i = d.eq(k, i);
    let lt_i_k = d.lt(i, k);
    let lt_k_j = d.lt(k, j);
    let eq_k_j = d.eq(k, j);
    let lt_j_k = d.lt(j, k);

    let branch_lt_i = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let fact = tau_eq_lt_i(d, i, j, k, h);
        let result = tau_close_involutive(d, i, j, k, k, k, fact, fact);
        d.lam_fv(h_fv, lt_k_i, result)
    };

    let branch_eq_i = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let fact_at_i = tau_eq_at_i(d, i, j);
        let fact_at_j = tau_eq_at_j(d, i, j, h_ij);
        let at_i = tau_close_involutive(d, i, j, i, j, i, fact_at_i, fact_at_j);
        let result = tau_transport_involutive(d, i, j, k, i, h, at_i);
        d.lam_fv(h_fv, eq_k_i, result)
    };

    let branch_gt_i = {
        let hg_fv = d.fresh_fvar();
        let hg = d.kernel().fvar(hg_fv);

        let tri_inner = super::prod::nat_trichotomy(d, k, j);
        let inner_lt_j = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let fact = tau_eq_between(d, i, j, k, hg, h2);
            let result = tau_close_involutive(d, i, j, k, k, k, fact, fact);
            d.lam_fv(h2_fv, lt_k_j, result)
        };
        let inner_rest = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);

            let inner_eq_j = {
                let h3_fv = d.fresh_fvar();
                let h3 = d.kernel().fvar(h3_fv);
                let fact_at_j = tau_eq_at_j(d, i, j, h_ij);
                let fact_at_i = tau_eq_at_i(d, i, j);
                let at_j = tau_close_involutive(d, i, j, j, i, j, fact_at_j, fact_at_i);
                let result = tau_transport_involutive(d, i, j, k, j, h3, at_j);
                d.lam_fv(h3_fv, eq_k_j, result)
            };
            let inner_gt_j = {
                let h3_fv = d.fresh_fvar();
                let h3 = d.kernel().fvar(h3_fv);
                let fact = tau_eq_gt_j(d, i, j, k, h_ij, h3);
                let result = tau_close_involutive(d, i, j, k, k, k, fact, fact);
                d.lam_fv(h3_fv, lt_j_k, result)
            };

            let body = d.const_app(
                p.logic.or_elim,
                &[eq_k_j, lt_j_k, goal, h2, inner_eq_j, inner_gt_j],
            );
            let or_rest2_ty = d.or(eq_k_j, lt_j_k);
            d.lam_fv(h2_fv, or_rest2_ty, body)
        };

        let or_rest2_ty = d.or(eq_k_j, lt_j_k);
        let body = d.const_app(
            p.logic.or_elim,
            &[lt_k_j, or_rest2_ty, goal, tri_inner, inner_lt_j, inner_rest],
        );
        d.lam_fv(hg_fv, lt_i_k, body)
    };

    let branch_rest = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = d.const_app(
            p.logic.or_elim,
            &[eq_k_i, lt_i_k, goal, h, branch_eq_i, branch_gt_i],
        );
        let or_rest_ty = d.or(eq_k_i, lt_i_k);
        d.lam_fv(h_fv, or_rest_ty, body)
    };

    let tri_outer = super::prod::nat_trichotomy(d, k, i);
    let or_rest_ty = d.or(eq_k_i, lt_i_k);
    let proof_body = d.const_app(
        p.logic.or_elim,
        &[
            lt_k_i,
            or_rest_ty,
            goal,
            tri_outer,
            branch_lt_i,
            branch_rest,
        ],
    );

    d.lam_fv(k_fv, nat, proof_body)
}

fn tau_bool_select_lt(
    d: &mut IntDev<'_>,
    cond: ExprId,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    ha: ExprId,
    hb: ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let p = d.int();
    let motive = {
        let sel_fv = d.fresh_fvar();
        let sel = d.kernel().fvar(sel_fv);
        let sv = d.bool_select_nat(sel, a, b);
        let body = d.lt(sv, n);
        d.lam_fv(sel_fv, bool_ty, body)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive, hb, ha, cond])
}

#[allow(clippy::too_many_arguments)]
fn tau_level4_lt(
    d: &mut IntDev<'_>,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    n: ExprId,
    hi: ExprId,
    hk: ExprId,
) -> ExprId {
    let cond = d.ble(k, j);
    tau_bool_select_lt(d, cond, i, k, n, hi, hk)
}
#[allow(clippy::too_many_arguments)]
fn tau_level3_lt(
    d: &mut IntDev<'_>,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    n: ExprId,
    hi: ExprId,
    hk: ExprId,
) -> ExprId {
    let level4 = tau_level4(d, i, j, k);
    let level4_lt = tau_level4_lt(d, i, j, k, n, hi, hk);
    let sk = d.succ(k);
    let cond = d.ble(sk, j);
    tau_bool_select_lt(d, cond, k, level4, n, hk, level4_lt)
}
#[allow(clippy::too_many_arguments)]
fn tau_level2_lt(
    d: &mut IntDev<'_>,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    n: ExprId,
    hi: ExprId,
    hj: ExprId,
    hk: ExprId,
) -> ExprId {
    let level3 = tau_level3(d, i, j, k);
    let level3_lt = tau_level3_lt(d, i, j, k, n, hi, hk);
    let cond = d.ble(k, i);
    tau_bool_select_lt(d, cond, j, level3, n, hj, level3_lt)
}
#[allow(clippy::too_many_arguments)]
fn tau_lt(
    d: &mut IntDev<'_>,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    n: ExprId,
    hi: ExprId,
    hj: ExprId,
    hk: ExprId,
) -> ExprId {
    let level2 = tau_level2(d, i, j, k);
    let level2_lt = tau_level2_lt(d, i, j, k, n, hi, hj, hk);
    let sk = d.succ(k);
    let cond = d.ble(sk, i);
    tau_bool_select_lt(d, cond, k, level2, n, hk, level2_lt)
}

/// `h_ij : Lt i j, h_jn : Lt j n ⊢ ∀ k, Lt k n → Lt (tau_raw i j k) n`.
fn tau_maps_into_forall(
    d: &mut IntDev<'_>,
    i: ExprId,
    j: ExprId,
    h_ij: ExprId,
    h_jn: ExprId,
    n: ExprId,
) -> ExprId {
    let p = d.int();
    let nat = d.nat_ty();
    let le_i_j = le_of_lt_local(d, i, j, h_ij);
    let hi = d.lemma(p.nat.lt_of_le_of_lt, &[i, j, n, le_i_j, h_jn]);
    let hj = h_jn;

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hk_fv = d.fresh_fvar();
    let hk = d.kernel().fvar(hk_fv);
    let hk_ty = d.lt(k, n);

    let result = tau_lt(d, i, j, k, n, hi, hj, hk);
    let inner = d.lam_fv(hk_fv, hk_ty, result);
    d.lam_fv(k_fv, nat, inner)
}

/// `ne_i : Not (Eq Nat k i), ne_j : Not (Eq Nat k j), h_ij : Lt i j ⊢
/// Eq Int (f k) (g k)`, for `g := fun x => f (tau_raw i j x)` — mirrors
/// `int_prelude/prod.rs`'s `general_swap_agree`, specialized to `f∘tau_raw`
/// in place of `point_swap`.
#[allow(clippy::too_many_arguments)]
fn tau_agree(
    d: &mut IntDev<'_>,
    f: ExprId,
    g: ExprId,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    ne_i: ExprId,
    ne_j: ExprId,
    h_ij: ExprId,
) -> ExprId {
    let fk = d.apply(f, &[k]);
    let gk = d.apply(g, &[k]);
    let target = d.ieq(fk, gk);
    let dis_i = super::prod::nat_lt_or_gt_of_ne(d, k, i, ne_i);
    let lt_ki = d.lt(k, i);
    let lt_ik = d.lt(i, k);

    let on_lt = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
        let eqp = tau_eq_lt_i(d, i, j, k, h);
        let traw = tau_raw(d, i, j, k);
        let cast = d.nat_eq_to_int(traw, k, eqp, &|d, x| d.apply(f, &[x]));
        d.isymm(gk, fk, cast)
    };
    let on_gt = &|d: &mut IntDev<'_>, h1: ExprId| -> ExprId {
        let dis_j = super::prod::nat_lt_or_gt_of_ne(d, k, j, ne_j);
        let lt_kj = d.lt(k, j);
        let lt_jk = d.lt(j, k);
        let on_between = &|d: &mut IntDev<'_>, h2: ExprId| -> ExprId {
            let eqp = tau_eq_between(d, i, j, k, h1, h2);
            let traw = tau_raw(d, i, j, k);
            let cast = d.nat_eq_to_int(traw, k, eqp, &|d, x| d.apply(f, &[x]));
            d.isymm(gk, fk, cast)
        };
        let on_gt_j = &|d: &mut IntDev<'_>, h2: ExprId| -> ExprId {
            let eqp = tau_eq_gt_j(d, i, j, k, h_ij, h2);
            let traw = tau_raw(d, i, j, k);
            let cast = d.nat_eq_to_int(traw, k, eqp, &|d, x| d.apply(f, &[x]));
            d.isymm(gk, fk, cast)
        };
        d.or_elim(lt_kj, lt_jk, target, dis_j, on_between, on_gt_j)
    };
    d.or_elim(lt_ki, lt_ik, target, dis_i, on_lt, on_gt)
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn case_b_body(
    d: &mut IntDev<'_>,
    bigp: ExprId,
    pos_bigp: ExprId,
    m: ExprId,
    f: ExprId,
    sigma: ExprId,
    inj: ExprId,
    maps: ExprId,
    fpf_p: ExprId,
    invol_p: ExprId,
    pairwise_p: ExprId,
    ih_lo: ExprId,
    i0: ExprId,        // literally `sigma sm`
    h_i0_lt_m: ExprId, // Lt i0 m
) -> ExprId {
    let p = d.int();
    let nat = d.nat_ty();
    let sm = d.succ(m);
    let n2 = d.succ(sm);
    let m_lt_sm = d.lemma(p.nat.lt_succ_self, &[m]);
    let sm_lt_n2 = d.lemma(p.nat.lt_succ_self, &[sm]);
    let le_sm_n2 = le_of_lt_local(d, sm, n2, sm_lt_n2);
    let m_lt_n2 = d.lemma(p.nat.lt_of_lt_of_le, &[m, sm, n2, m_lt_sm, le_sm_n2]);

    let tau_fn = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = tau_raw(d, i0, m, k);
        d.lam_fv(k_fv, nat, body)
    };
    let t_inv = tau_involutive_forall(d, i0, m, h_i0_lt_m);
    let t_maps_n2 = tau_maps_into_forall(d, i0, m, h_i0_lt_m, m_lt_n2, n2);

    let sigma_prime = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let tk = d.apply(tau_fn, &[k]);
        let stk = d.apply(sigma, &[tk]);
        let body = d.apply(tau_fn, &[stk]);
        d.lam_fv(k_fv, nat, body)
    };
    let g = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let tk = d.apply(tau_fn, &[k]);
        let body = d.apply(f, &[tk]);
        d.lam_fv(k_fv, nat, body)
    };

    let inj_prime = d.const_app(
        p.nat.conjugate_injective,
        &[tau_fn, sigma, n2, t_inv, t_maps_n2, inj],
    );
    let maps_prime = d.const_app(
        p.nat.conjugate_maps_into,
        &[tau_fn, sigma, n2, t_maps_n2, maps],
    );

    let fpf_prime = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let hk_ty = d.lt(k, n2);
        let sigma_prime_k = d.apply(sigma_prime, &[k]);
        let eq_ty = d.eq(sigma_prime_k, k);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        let tk = d.apply(tau_fn, &[k]);
        let a_val = d.apply(sigma, &[tk]);
        let b_val = d.apply(tau_fn, &[a_val]);
        let congr_t_heq = d.congr(b_val, k, heq, &|d, x| d.apply(tau_fn, &[x]));
        let t_b = d.apply(tau_fn, &[b_val]);
        let t_inv_a = d.apply(t_inv, &[a_val]);
        let t_b_rev = d.symm(t_b, a_val, t_inv_a);
        let a_val_eq_tk = d.trans(a_val, t_b, tk, t_b_rev, congr_t_heq);
        let tk_lt_n2 = d.apply(t_maps_n2, &[k, hk]);
        let fpf_at_tk = d.apply(fpf_p, &[tk, tk_lt_n2]);
        let false_pf = d.apply(fpf_at_tk, &[a_val_eq_tk]);

        let with_heq = d.lam_fv(heq_fv, eq_ty, false_pf);
        let with_hk = d.lam_fv(hk_fv, hk_ty, with_heq);
        d.lam_fv(k_fv, nat, with_hk)
    };

    let invol_prime = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let hk_ty = d.lt(k, n2);

        let tk = d.apply(tau_fn, &[k]);
        let a_val = d.apply(sigma, &[tk]);
        let b_val = d.apply(tau_fn, &[a_val]);
        let tb_val = d.apply(tau_fn, &[b_val]);
        let t_inv_a = d.apply(t_inv, &[a_val]);
        let step2 = d.congr(tb_val, a_val, t_inv_a, &|d, x| d.apply(sigma, &[x]));
        let sigma_tb = d.apply(sigma, &[tb_val]);
        let sigma_a = d.apply(sigma, &[a_val]);
        let tk_lt_n2 = d.apply(t_maps_n2, &[k, hk]);
        let step4 = d.apply(invol_p, &[tk, tk_lt_n2]);
        let step5 = d.trans(sigma_tb, sigma_a, tk, step2, step4);
        let step6 = d.congr(sigma_tb, tk, step5, &|d, x| d.apply(tau_fn, &[x]));
        let t_sigma_tb = d.apply(tau_fn, &[sigma_tb]);
        let t_tk = d.apply(tau_fn, &[tk]);
        let t_inv_k = d.apply(t_inv, &[k]);
        let step8 = d.trans(t_sigma_tb, t_tk, k, step6, t_inv_k);

        let with_hk = d.lam_fv(hk_fv, hk_ty, step8);
        d.lam_fv(k_fv, nat, with_hk)
    };

    let pairwise_prime = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let hk_ty = d.lt(k, n2);

        let tk = d.apply(tau_fn, &[k]);
        let a_val = d.apply(sigma, &[tk]);
        let b_val = d.apply(tau_fn, &[a_val]);
        let t_b = d.apply(tau_fn, &[b_val]);
        let t_inv_a = d.apply(t_inv, &[a_val]);

        let tk_lt_n2 = d.apply(t_maps_n2, &[k, hk]);
        let base_pairwise = d.apply(pairwise_p, &[tk, tk_lt_n2]);
        let f_tk = d.apply(f, &[tk]);
        let f_a = d.apply(f, &[a_val]);
        let f_tb = d.apply(f, &[t_b]);
        let f_a_eq_f_tb = {
            let sym = d.symm(t_b, a_val, t_inv_a);
            d.nat_eq_to_int(a_val, t_b, sym, &|d, x| d.apply(f, &[x]))
        };
        let result = d.int_eq_rewrite(f_a, f_tb, f_a_eq_f_tb, base_pairwise, &|d, x| {
            let pr = d.imul(f_tk, x);
            let one_i = d.ione();
            super::modeq::imodeq(d, bigp, pr, one_i)
        });
        let with_hk = d.lam_fv(hk_fv, hk_ty, result);
        d.lam_fv(k_fv, nat, with_hk)
    };

    let sigma_prime_m_eq_sm = {
        let tau_m_eq_i0 = tau_eq_at_j(d, i0, m, h_i0_lt_m);
        let traw_m = tau_raw(d, i0, m, m);
        let congr1 = d.congr(traw_m, i0, tau_m_eq_i0, &|d, x| d.apply(sigma, &[x]));
        let sigma_i0_eq_sm = d.apply(invol_p, &[sm, sm_lt_n2]);
        let sigma_traw_m = d.apply(sigma, &[traw_m]);
        let sigma_i0 = d.apply(sigma, &[i0]);
        let step2 = d.trans(sigma_traw_m, sigma_i0, sm, congr1, sigma_i0_eq_sm);
        let tau_sm_eq_sm = tau_eq_gt_j(d, i0, m, sm, h_i0_lt_m, m_lt_sm);
        let step3 = d.congr(sigma_traw_m, sm, step2, &|d, x| d.apply(tau_fn, &[x]));
        let tau_fn_sigma_traw_m = d.apply(tau_fn, &[sigma_traw_m]);
        let tau_fn_sm = d.apply(tau_fn, &[sm]);
        d.trans(tau_fn_sigma_traw_m, tau_fn_sm, sm, step3, tau_sm_eq_sm)
    };
    let sigma_prime_sm_eq_m = {
        let tau_sm_eq_sm = tau_eq_gt_j(d, i0, m, sm, h_i0_lt_m, m_lt_sm);
        let traw_sm = tau_raw(d, i0, m, sm);
        let congr1 = d.congr(traw_sm, sm, tau_sm_eq_sm, &|d, x| d.apply(sigma, &[x]));
        let sigma_traw_sm = d.apply(sigma, &[traw_sm]);
        let tau_i0_eq_m = tau_eq_at_i(d, i0, m);
        let step2 = d.congr(sigma_traw_sm, i0, congr1, &|d, x| d.apply(tau_fn, &[x]));
        let tau_fn_sigma_traw_sm = d.apply(tau_fn, &[sigma_traw_sm]);
        let tau_fn_i0 = d.apply(tau_fn, &[i0]);
        d.trans(tau_fn_sigma_traw_sm, tau_fn_i0, m, step2, tau_i0_eq_m)
    };

    let peeled = peel_and_close(
        d,
        bigp,
        pos_bigp,
        m,
        g,
        sigma_prime,
        inj_prime,
        maps_prime,
        fpf_prime,
        invol_prime,
        pairwise_prime,
        sigma_prime_m_eq_sm,
        sigma_prime_sm_eq_m,
        ih_lo,
    );

    let g_i0_eq_f_m = {
        let tau_i0_eq_m = tau_eq_at_i(d, i0, m);
        let traw_i0 = tau_raw(d, i0, m, i0);
        d.nat_eq_to_int(traw_i0, m, tau_i0_eq_m, &|d, x| d.apply(f, &[x]))
    };
    let g_m_eq_f_i0 = {
        let tau_m_eq_i0 = tau_eq_at_j(d, i0, m, h_i0_lt_m);
        let traw_m = tau_raw(d, i0, m, m);
        d.nat_eq_to_int(traw_m, i0, tau_m_eq_i0, &|d, x| d.apply(f, &[x]))
    };
    let elsewhere = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let nei_fv = d.fresh_fvar();
        let nei = d.kernel().fvar(nei_fv);
        let nei_ty = {
            let e = d.eq(k, i0);
            d.not(e)
        };
        let nej_fv = d.fresh_fvar();
        let nej = d.kernel().fvar(nej_fv);
        let nej_ty = {
            let e = d.eq(k, m);
            d.not(e)
        };
        let result = tau_agree(d, f, g, i0, m, k, nei, nej, h_i0_lt_m);
        let inner = d.lam_fv(nej_fv, nej_ty, result);
        let with_nei = d.lam_fv(nei_fv, nei_ty, inner);
        d.lam_fv(k_fv, nat, with_nei)
    };

    let swap_eq = d.const_app(
        p.prod_range_swap,
        &[
            f,
            g,
            i0,
            m,
            n2,
            h_i0_lt_m,
            m_lt_n2,
            g_i0_eq_f_m,
            g_m_eq_f_i0,
            elsewhere,
        ],
    );
    let f_range = d.const_app(p.prod_range, &[f, n2]);
    let g_range = d.const_app(p.prod_range, &[g, n2]);
    let swap_eq_rev = d.isymm(f_range, g_range, swap_eq);
    d.int_eq_rewrite(g_range, f_range, swap_eq_rev, peeled, &|d, x| {
        let one_i = d.ione();
        super::modeq::imodeq(d, bigp, x, one_i)
    })
}

// --- assembling the step case: `family (succ (succ m))` from `family m` ----

#[allow(clippy::too_many_lines)]
fn family_succ_succ_proof(
    d: &mut IntDev<'_>,
    bigp: ExprId,
    pos_bigp: ExprId,
    m: ExprId,
    ih_lo: ExprId,
) -> ExprId {
    let p = d.int();
    let fn_int_ty = nat_to_int_ty(d);
    let fn_nat_ty = nat_to_nat_ty(d);

    let sm = d.succ(m);
    let n2 = d.succ(sm);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let sigma_fv = d.fresh_fvar();
    let sigma = d.kernel().fvar(sigma_fv);

    let inj_ty = d.const_app(p.nat.injective_on, &[sigma, n2]);
    let maps_ty = d.const_app(p.nat.maps_into, &[sigma, n2]);
    let fpf = fpf_ty(d, sigma, n2);
    let invol = invol_ty(d, sigma, n2);
    let pairwise = pairwise_ty(d, bigp, f, sigma, n2);

    let inj_fv = d.fresh_fvar();
    let inj = d.kernel().fvar(inj_fv);
    let maps_fv = d.fresh_fvar();
    let maps = d.kernel().fvar(maps_fv);
    let fpf_fv = d.fresh_fvar();
    let fpf_p = d.kernel().fvar(fpf_fv);
    let invol_fv = d.fresh_fvar();
    let invol_p = d.kernel().fvar(invol_fv);
    let pairwise_fv = d.fresh_fvar();
    let pairwise_p = d.kernel().fvar(pairwise_fv);

    let concl = {
        let pr = d.const_app(p.prod_range, &[f, n2]);
        let one_i = d.ione();
        super::modeq::imodeq(d, bigp, pr, one_i)
    };

    let sm_lt_n2 = d.lemma(p.nat.lt_succ_self, &[sm]);
    let i0 = d.apply(sigma, &[sm]);
    let sigma_i0_eq_sm = d.apply(invol_p, &[sm, sm_lt_n2]);

    let i0_lt_n2 = d.apply(maps, &[sm, sm_lt_n2]);
    let i0_ne_sm = d.apply(fpf_p, &[sm, sm_lt_n2]);
    let le_i0_sm = d.lemma(p.nat.le_of_lt_succ, &[i0, sm, i0_lt_n2]);
    let lt_i0_sm = lt_of_le_ne(d, i0, sm, le_i0_sm, i0_ne_sm);
    let le_i0_m = d.lemma(p.nat.le_of_lt_succ, &[i0, m, lt_i0_sm]);
    let case_pf = d.lemma(p.nat.lt_or_eq_of_le, &[i0, m, le_i0_m]);

    let lt_i0_m_ty = d.lt(i0, m);
    let eq_i0_m_ty = d.eq(i0, m);

    let body = d.or_elim(
        lt_i0_m_ty,
        eq_i0_m_ty,
        concl,
        case_pf,
        &|d, h_i0_lt_m| {
            case_b_body(
                d, bigp, pos_bigp, m, f, sigma, inj, maps, fpf_p, invol_p, pairwise_p, ih_lo, i0,
                h_i0_lt_m,
            )
        },
        &|d, h_i0_eq_m| {
            case_a_body(
                d,
                bigp,
                pos_bigp,
                m,
                f,
                sigma,
                inj,
                maps,
                fpf_p,
                invol_p,
                pairwise_p,
                sigma_i0_eq_sm,
                i0,
                h_i0_eq_m,
                ih_lo,
            )
        },
    );

    let with_pairwise = d.lam_fv(pairwise_fv, pairwise, body);
    let with_invol = d.lam_fv(invol_fv, invol, with_pairwise);
    let with_fpf = d.lam_fv(fpf_fv, fpf, with_invol);
    let with_maps = d.lam_fv(maps_fv, maps_ty, with_fpf);
    let with_inj = d.lam_fv(inj_fv, inj_ty, with_maps);
    let with_sigma = d.lam_fv(sigma_fv, fn_nat_ty, with_inj);
    d.lam_fv(f_fv, fn_int_ty, with_sigma)
}

// --- the top-level declaration ---------------------------------------------

/// Admit `Int.prod_range_pairing_collapse`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_prod_range_pairing_collapse(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat = d.nat_ty();

    let bigp_fv = d.fresh_fvar();
    let bigp = d.kernel().fvar(bigp_fv);
    let zero_i = d.izero();
    let pos_ty = d.ilt(zero_i, bigp);
    let pos_fv = d.fresh_fvar();
    let pos_bigp = d.kernel().fvar(pos_fv);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let strengthened_motive = |d: &mut IntDev<'_>, x: ExprId| strengthened_stmt(d, bigp, x);
    let base = |d: &mut IntDev<'_>| -> ExprId {
        let p = d.int();
        let zero = d.zero();
        let one_n = d.succ(zero);
        let fam0 = family_zero_proof(d, bigp);
        let fam1 = family_one_proof(d, bigp);
        let fam0_ty = family_stmt(d, bigp, zero);
        let fam1_ty = family_stmt(d, bigp, one_n);
        d.const_app(p.logic.and_intro, &[fam0_ty, fam1_ty, fam0, fam1])
    };
    let step = |d: &mut IntDev<'_>, m: ExprId, ih: ExprId| -> ExprId {
        let p = d.int();
        let fam_m_ty = family_stmt(d, bigp, m);
        let sm = d.succ(m);
        let fam_sm_ty = family_stmt(d, bigp, sm);
        let ih_lo = d.and_left(fam_m_ty, fam_sm_ty, ih);
        let ih_hi = d.and_right(fam_m_ty, fam_sm_ty, ih);
        let fam_ssm = family_succ_succ_proof(d, bigp, pos_bigp, m, ih_lo);
        let ssm = d.succ(sm);
        let fam_ssm_ty = family_stmt(d, bigp, ssm);
        d.const_app(p.logic.and_intro, &[fam_sm_ty, fam_ssm_ty, ih_hi, fam_ssm])
    };
    let strengthened_proof = d.induct(&strengthened_motive, &base, &step, n);

    let fam_n_ty = family_stmt(d, bigp, n);
    let sn = d.succ(n);
    let fam_sn_ty = family_stmt(d, bigp, sn);
    let fam_n = d.and_left(fam_n_ty, fam_sn_ty, strengthened_proof);

    let value = {
        let with_n = d.lam_fv(n_fv, nat, fam_n);
        let with_pos = d.lam_fv(pos_fv, pos_ty, with_n);
        d.lam_fv(bigp_fv, int_ty, with_pos)
    };
    let ty = {
        let with_n = d.pi_fv(n_fv, nat, fam_n_ty);
        let with_pos = d.arrow(pos_ty, with_n);
        d.pi_fv(bigp_fv, int_ty, with_pos)
    };
    d.declare_theorem(p.prod_range_pairing_collapse, ty, value)
}

// ============================================================================
// `Int.factorial_interior_modeq_one` — the reindex, landed 2026-08-24.
//
// `Nat.inverseIndex p`'s two fixed points sit at the domain's first and last
// index (`0` and `p-2`, `declare_inverse_index_fixes_zero`/`_fixes_last`), so
// the interior `{1,…,p-3}` reindexes down to `[0,p-3)` via `σ' i := σ(i+1) -
// 1`, and `prod_range_pairing_collapse` applies directly to `σ'` and `G i :=
// ofNat(succ(succ i))` (`= F(i+1)` for `F` the factor `Int.factorial`
// unfolds to). `SigmaPrimeAt` below computes, for one interior index `i` (a
// hypothesis `i < p-3` already in hand), every fact `σ'` needs at that index;
// `sigma_prime_at`'s own doc comment spells out the arithmetic. The four
// remaining premises `prod_range_pairing_collapse` needs are then: `MapsInto`
// and fixed-point-freedom straight from the bundle; `InjectiveOn`, derived
// generically from involution (`injective_of_involutive_local` — any
// involution is automatically injective on its own domain, independent of
// anything else about it); and involution itself, which calls
// `sigma_prime_at` a SECOND time at `j := σ' i` and chains the original `σ`'s
// own involution at `k := succ i` through the reindex.
// ============================================================================

/// `h : Not (Eq Nat a b) ⊢ Not (Eq Nat b a)`.
fn ne_symm(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let heq_ty = d.eq(b, a);
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);
    let flipped = d.symm(b, a, heq); // Eq Nat a b
    let false_pf = d.apply(h, &[flipped]);
    d.lam_fv(heq_fv, heq_ty, false_pf)
}

/// From `invol : ∀ k, Lt k n → Eq Nat (sigma (sigma k)) k`, derive
/// `InjectiveOn sigma n` — an involution is automatically injective on its
/// own domain (`sigma i = sigma j` gives `i = sigma(sigma i) = sigma(sigma
/// j) = j`, using involution at `i` and at `j` and nothing else about
/// `sigma`), so this needs no fixed-point-freedom, no `MapsInto`, nothing
/// specific to `Nat.inverseIndex` at all.
pub(super) fn injective_of_involutive_local(
    d: &mut IntDev<'_>,
    sigma: ExprId,
    invol: ExprId,
    n: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let hi_fv = d.fresh_fvar();
    let hi_ty = d.lt(i, n);
    let hi = d.kernel().fvar(hi_fv);
    let hj_fv = d.fresh_fvar();
    let hj_ty = d.lt(j, n);
    let hj = d.kernel().fvar(hj_fv);

    let si = d.apply(sigma, &[i]);
    let sj = d.apply(sigma, &[j]);
    let heq_ty = d.eq(si, sj);
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);

    let invol_i = d.apply(invol, &[i, hi]); // Eq Nat (sigma si) i
    let invol_j = d.apply(invol, &[j, hj]); // Eq Nat (sigma sj) j
    let ssi = d.apply(sigma, &[si]);
    let ssj = d.apply(sigma, &[sj]);

    let invol_i_rev = d.symm(ssi, i, invol_i); // Eq Nat i ssi
    let congr_heq = d.congr(si, sj, heq, &|d, x| d.apply(sigma, &[x])); // Eq Nat ssi ssj
    let i_eq_ssj = d.trans(i, ssi, ssj, invol_i_rev, congr_heq);
    let i_eq_j = d.trans(i, ssj, j, i_eq_ssj, invol_j);

    let with_heq = d.lam_fv(heq_fv, heq_ty, i_eq_j);
    let with_hj = d.lam_fv(hj_fv, hj_ty, with_heq);
    let with_hi = d.lam_fv(hi_fv, hi_ty, with_hj);
    let with_j = d.lam_fv(j_fv, nat, with_hi);
    d.lam_fv(i_fv, nat, with_j)
}

/// `ModEq (ofNat pp) (mul (F k) (F (inverseIndex pp k))) one`, for `F := fun
/// k => ofNat (succ k)`, given `k < p - 1`. Exactly the pointwise congruence
/// [`declare_factorial_sq_modeq_one`]'s own closure proves inline for `k`
/// ranging over the WHOLE domain `[0, p-1)` (`Int.mul_inv_of_pow` plus the
/// `inverseIndex k = natAbs(...) - 1` unfold); factored out here as its own
/// function, taking the bound proof directly, rather than shared with that
/// closure's captured state.
#[allow(clippy::too_many_arguments)]
fn pairwise_modeq_general(
    d: &mut IntDev<'_>,
    pp: ExprId,
    prime_proof: ExprId,
    pm1: ExprId,
    k: ExprId,
    hk_lt_pm1: ExprId,
) -> ExprId {
    let p = d.int();
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let one_le_pp = nat_prime_pos(d, pp, prime_proof);
    let pos_big_p = one_le_pp;
    let big_p = d.of_nat(pp);
    let one_i = d.ione();

    let sk = d.succ(k);
    let fk = d.of_nat(sk);

    let mono_fn = d.lemma(p.nat.succ_le_succ, &[sk, pm1]);
    let mono = d.apply(mono_fn, &[hk_lt_pm1]); // Le (succ sk) (succ pm1)
    let cancel1 = d.lemma(p.nat.sub_add_cancel, &[one_nat, pp, one_le_pp]); // ~ Eq Nat (succ pm1) pp
    let succ_pm1 = d.succ(pm1);
    let ub_k = d.nat_rewrite(succ_pm1, pp, cancel1, mono, &|d, x| {
        let s = d.succ(sk);
        d.le(s, x)
    });
    let pos_sk = d.lemma(p.nat.zero_lt_succ, &[k]);

    let mip_k = d.const_app(p.mul_inv_of_pow, &[pp, sk, prime_proof, pos_sk, ub_k]);

    let pm2 = d.sub(pp, two_nat);
    let pw_k = d.ipow(fk, pm2);
    let r_k = d.iemod(pw_k, big_p);
    let mag_k = {
        let f = p.nat_abs;
        d.const_app(f, &[r_k])
    };

    let mag_k_ne = mag_ne_zero(d, pp, sk, prime_proof, pos_sk, ub_k);
    let mag_k_pos = pos_of_ne_zero(d, mag_k, mag_k_ne);
    let sk_raw = d.sub(mag_k, one_nat);
    let succ_sk_raw = d.succ(sk_raw);
    let cancel_k = d.lemma(p.nat.sub_add_cancel, &[one_nat, mag_k, mag_k_pos]);

    let ne_big_p = int_ne_zero_of_pos(d, big_p, pos_big_p);
    let r_k_nonneg = d.const_app(p.emod_nonneg, &[pw_k, big_p, ne_big_p]);

    let ofnat_succ_sk_raw = d.of_nat(succ_sk_raw);
    let ofnat_mag_k = d.of_nat(mag_k);
    let bridge_a = d.nat_eq_to_int(succ_sk_raw, mag_k, cancel_k, &|d, y| d.of_nat(y));
    let bridge_b = d.const_app(p.of_nat_nat_abs_of_nonneg, &[r_k, r_k_nonneg]);
    let f_sk_eq_rk = d.itrans(ofnat_succ_sk_raw, ofnat_mag_k, r_k, bridge_a, bridge_b);

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

    let scaled = d.const_app(
        p.mod_eq_mul_left,
        &[big_p, ofnat_succ_sk_raw, pw_k, fk, pos_big_p, modeq_fsk_pwk],
    );
    let lhs_scaled = d.imul(fk, ofnat_succ_sk_raw);
    let mid_scaled = d.imul(fk, pw_k);
    d.const_app(
        p.mod_eq_trans,
        &[big_p, lhs_scaled, mid_scaled, one_i, scaled, mip_k],
    )
}

/// Bundle of facts about `Nat.inverseIndex`'s interior reindex `σ' i := sub
/// (Nat.inverseIndex pp (succ i)) one`, computed at one interior index `i`
/// (under a hypothesis `i < pm3`, `pm3 := sub (sub pp 2) 1`).
struct SigmaPrimeAt {
    /// `succ i` — the original index `σ` reads through.
    k: ExprId,
    /// `Nat.inverseIndex pp k`.
    sigma_k: ExprId,
    /// `Eq Nat (sigma (sigma k)) k` — the original `σ`'s own involution at
    /// `k` (needs `k < pm1`, [`hk_lt_pm1`](Self::hk_lt_pm1)).
    invol_k: ExprId,
    /// `Lt k pm1` — `k`'s membership in `σ`'s own full domain.
    hk_lt_pm1: ExprId,
    /// `sub sigma_k one` — `σ' i` itself.
    val: ExprId,
    /// `Eq Nat (succ val) sigma_k`.
    succ_val_eq_sigma_k: ExprId,
    /// `Lt val pm3` — `σ'` maps the interior into itself.
    maps: ExprId,
    /// `Not (Eq Nat val i)` — `σ'` is fixed-point-free on the interior.
    fpf: ExprId,
}

/// Build [`SigmaPrimeAt`] for index `i` under `hi : Lt i pm3`.
///
/// `k := succ i` is `σ`'s own index (`0 < k` is `hi`'s own `zero_lt_succ`;
/// `k < p-2` follows from `hi` — the derivation, spelled out: `hi` gives `k ≤
/// pm3`; `pm3 ≤ pm2` unconditionally (`Nat.sub_le`, true even when `pm2 = 0`
/// truncates); so `1 ≤ pm3 ≤ pm2`, i.e. `pm2 > 0`, so `succ pm3 = pm2`
/// (`Nat.sub_add_cancel`); `succ_le_succ` on `k ≤ pm3` then rewrites, through
/// that equation, to `k < pm2`). `k < p-1` follows the same way from `pm2 ≤
/// pm1` ([`succ_pm2_eq_pm1`]).
///
/// `σ k` avoids both of `σ`'s fixed points: if `σ k = 0`, applying `σ` to
/// both sides and using `σ`'s own involution at `k` and
/// [`declare_inverse_index_fixes_zero`] forces `k = 0`, contradicting `0 <
/// k`; the same argument against [`declare_inverse_index_fixes_last`] rules
/// out `σ k = p-2`. So `0 < σ k < p-2`, and `σ' i := σ k - 1` lands back in
/// `[0, pm3)` — this is [`maps`](SigmaPrimeAt::maps).
///
/// Fixed-point-freedom of `σ'` at `i` transports directly from
/// [`declare_inverse_index_interior_fixed_point_free`] at `k` (`0 < k < p-2`,
/// exactly what this function already established): `σ' i = i` would give
/// `σ k = succ(σ' i) = succ i = k`, contradicting that lemma.
///
/// No case is split anywhere in this construction on whether the interior is
/// empty (`p = 2` or `p = 3`) — every step only uses facts already implied by
/// `hi : Lt i pm3`, so those primes are simply never reached (the hypothesis
/// `i < pm3` is never inhabited when `pm3 = 0`).
#[allow(clippy::too_many_lines)]
fn sigma_prime_at(
    d: &mut IntDev<'_>,
    pp: ExprId,
    prime_proof: ExprId,
    i: ExprId,
    hi: ExprId,
) -> SigmaPrimeAt {
    let p = d.int();
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let zero = d.zero();
    let pm1 = d.sub(pp, one_nat);
    let pm2 = d.sub(pp, two_nat);
    let pm3 = d.sub(pm2, one_nat);

    let k = d.succ(i);

    // pm2 > 0, hence succ pm3 = pm2.
    let one_le_k = d.lemma(p.nat.zero_lt_succ, &[i]); // Le one_nat k
    let one_le_pm3 = d.lemma(p.nat.le_trans, &[one_nat, k, pm3, one_le_k, hi]); // Le one_nat pm3
    let pm3_le_pm2 = d.lemma(p.nat.sub_le, &[pm2, one_nat]); // Le pm3 pm2
    let pos_pm2 = d.lemma(p.nat.le_trans, &[one_nat, pm3, pm2, one_le_pm3, pm3_le_pm2]); // Le one_nat pm2
    let succ_pm3_eq_pm2 = d.lemma(p.nat.sub_add_cancel, &[one_nat, pm2, pos_pm2]); // ~ Eq Nat (succ pm3) pm2
    let succ_pm3 = d.succ(pm3);

    // hk_lo : Lt zero k.
    let hk_lo = d.lemma(p.nat.zero_lt_succ, &[i]);

    // hk_hi : Lt k pm2.
    let succ_k_le_succ_pm3 = d.lemma(p.nat.succ_le_succ, &[k, pm3, hi]); // Le (succ k) (succ pm3)
    let hk_hi = d.nat_rewrite(
        succ_pm3,
        pm2,
        succ_pm3_eq_pm2,
        succ_k_le_succ_pm3,
        &|d, x| {
            let sk = d.succ(k);
            d.le(sk, x)
        },
    );

    // hk_lt_pm1 : Lt k pm1, via pm2 ≤ pm1.
    let succ_pm2_eq_pm1_pf = succ_pm2_eq_pm1(d, pp, prime_proof); // Eq Nat (succ pm2) pm1
    let succ_pm2 = d.succ(pm2);
    let le_pm2_succ_pm2 = d.lemma(p.nat.le_succ, &[pm2]); // Le pm2 (succ pm2)
    let le_pm2_pm1 = d.nat_rewrite(
        succ_pm2,
        pm1,
        succ_pm2_eq_pm1_pf,
        le_pm2_succ_pm2,
        &|d, x| d.le(pm2, x),
    );
    let sk_for_hk_hi = d.succ(k);
    let hk_lt_pm1 = d.lemma(p.nat.le_trans, &[sk_for_hk_hi, pm2, pm1, hk_hi, le_pm2_pm1]);

    // sigma_k and its involution at k.
    let sigma_k = d.const_app(p.inverse_index, &[pp, k]);
    let invol_k = d.const_app(p.inverse_index_involutive, &[pp, k, prime_proof, hk_lt_pm1]); // Eq Nat (sigma sigma_k) k

    // sigma_k ≠ zero.
    let sigma_k_ne_zero = {
        let heq_ty = d.eq(sigma_k, zero);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let sigma_zero = d.const_app(p.inverse_index, &[pp, zero]);
        let invol_k_rewritten = d.nat_rewrite(sigma_k, zero, heq, invol_k, &|d, x| {
            let sx = d.const_app(p.inverse_index, &[pp, x]);
            d.eq(sx, k)
        }); // Eq Nat sigma_zero k
        let fixes_zero_pf = d.const_app(p.inverse_index_fixes_zero, &[pp, prime_proof]); // Eq Nat sigma_zero zero
        let k_eq_sigma_zero = d.symm(sigma_zero, k, invol_k_rewritten); // Eq Nat k sigma_zero
        let k_eq_zero = d.trans(k, sigma_zero, zero, k_eq_sigma_zero, fixes_zero_pf); // Eq Nat k zero
        let zero_eq_k = d.symm(k, zero, k_eq_zero);
        let ne_zero_k = ne_of_lt_local(d, zero, k, hk_lo); // Not (Eq Nat zero k)
        let false_pf = d.apply(ne_zero_k, &[zero_eq_k]);
        d.lam_fv(heq_fv, heq_ty, false_pf)
    };

    // sigma_k ≠ pm2.
    let sigma_k_ne_pm2 = {
        let heq_ty = d.eq(sigma_k, pm2);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let sigma_pm2 = d.const_app(p.inverse_index, &[pp, pm2]);
        let invol_k_rewritten = d.nat_rewrite(sigma_k, pm2, heq, invol_k, &|d, x| {
            let sx = d.const_app(p.inverse_index, &[pp, x]);
            d.eq(sx, k)
        }); // Eq Nat sigma_pm2 k
        let fixes_last_pf = d.const_app(p.inverse_index_fixes_last, &[pp, prime_proof]); // Eq Nat sigma_pm2 pm2
        let k_eq_sigma_pm2 = d.symm(sigma_pm2, k, invol_k_rewritten); // Eq Nat k sigma_pm2
        let k_eq_pm2 = d.trans(k, sigma_pm2, pm2, k_eq_sigma_pm2, fixes_last_pf); // Eq Nat k pm2
        let ne_k_pm2 = ne_of_lt_local(d, k, pm2, hk_hi); // Not (Eq Nat k pm2)
        let false_pf = d.apply(ne_k_pm2, &[k_eq_pm2]);
        d.lam_fv(heq_fv, heq_ty, false_pf)
    };

    // 0 < sigma_k < pm2.
    let zero_le_sigma_k = d.lemma(p.nat.zero_le, &[sigma_k]);
    let zero_ne_sigma_k = ne_symm(d, sigma_k, zero, sigma_k_ne_zero);
    let sigma_k_pos = lt_of_le_ne(d, zero, sigma_k, zero_le_sigma_k, zero_ne_sigma_k);

    let maps_sigma = d.const_app(p.inverse_index_maps_into, &[pp, prime_proof]);
    let sigma_k_lt_pm1 = d.apply(maps_sigma, &[k, hk_lt_pm1]); // Lt sigma_k pm1

    let succ_pm2_eq_pm1_rev = d.symm(succ_pm2, pm1, succ_pm2_eq_pm1_pf); // Eq Nat pm1 succ_pm2
    let sigma_k_lt_succ_pm2 = d.nat_rewrite(
        pm1,
        succ_pm2,
        succ_pm2_eq_pm1_rev,
        sigma_k_lt_pm1,
        &|d, x| d.lt(sigma_k, x),
    ); // Le (succ sigma_k) (succ pm2)
    let le_sigma_k_pm2 = d.lemma(p.nat.le_of_lt_succ, &[sigma_k, pm2, sigma_k_lt_succ_pm2]);
    let sigma_k_lt_pm2 = lt_of_le_ne(d, sigma_k, pm2, le_sigma_k_pm2, sigma_k_ne_pm2);

    // val := sigma_k - 1 ; succ val = sigma_k.
    let val = d.sub(sigma_k, one_nat);
    let succ_val_eq_sigma_k = d.lemma(p.nat.sub_add_cancel, &[one_nat, sigma_k, sigma_k_pos]); // ~ Eq Nat (succ val) sigma_k

    // maps : Lt val pm3.
    let succ_pm3_eq_pm2_rev = d.symm(succ_pm3, pm2, succ_pm3_eq_pm2); // Eq Nat pm2 succ_pm3
    let sigma_k_lt_succ_pm3 = d.nat_rewrite(
        pm2,
        succ_pm3,
        succ_pm3_eq_pm2_rev,
        sigma_k_lt_pm2,
        &|d, x| d.lt(sigma_k, x),
    ); // Le (succ sigma_k) (succ pm3)
    let peel2 = d.lemma(p.nat.le_of_succ_le_succ, &[sigma_k, pm3]);
    let le_sigma_k_pm3 = d.apply(peel2, &[sigma_k_lt_succ_pm3]); // Le sigma_k pm3
    let succ_val = d.succ(val);
    let succ_val_eq_sigma_k_rev = d.symm(succ_val, sigma_k, succ_val_eq_sigma_k); // Eq Nat sigma_k succ_val
    let maps = d.nat_rewrite(
        sigma_k,
        succ_val,
        succ_val_eq_sigma_k_rev,
        le_sigma_k_pm3,
        &|d, x| d.le(x, pm3),
    ); // Le succ_val pm3 = Lt val pm3

    // fpf : Not (Eq Nat val i).
    let sigma_neq_k = d.const_app(
        p.inverse_index_interior_fixed_point_free,
        &[pp, prime_proof, k, hk_lo, hk_hi],
    ); // Not (Eq Nat sigma_k k)
    let fpf = {
        let heq_ty = d.eq(val, i);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let congr_succ = d.congr(val, i, heq, &|d, x| d.succ(x)); // Eq Nat succ_val (succ i) = Eq Nat succ_val k
        let succ_val_eq_sigma_k_rev2 = d.symm(succ_val, sigma_k, succ_val_eq_sigma_k); // Eq Nat sigma_k succ_val
        let sigma_k_eq_k = d.trans(sigma_k, succ_val, k, succ_val_eq_sigma_k_rev2, congr_succ); // Eq Nat sigma_k k
        let false_pf = d.apply(sigma_neq_k, &[sigma_k_eq_k]);
        d.lam_fv(heq_fv, heq_ty, false_pf)
    };

    SigmaPrimeAt {
        k,
        sigma_k,
        invol_k,
        hk_lt_pm1,
        val,
        succ_val_eq_sigma_k,
        maps,
        fpf,
    }
}

/// `Int.factorial_interior_modeq_one :
/// ∀ p, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) →
///   ModEq (ofNat p) (prodRange (fun i => ofNat (succ (succ i))) (p-3)) one`
///
/// See this module's doc section above [`sigma_prime_at`] for the route.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_factorial_interior_modeq_one(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    d.theorem(p.factorial_interior_modeq_one, 1, &|d, v| {
        let pp = v[0];
        let prime_ty = prime_condition(d, pp);

        let one_nat = d.num(1);
        let two_nat = d.num(2);
        let pm1 = d.sub(pp, one_nat);
        let pm2 = d.sub(pp, two_nat);
        let pm3 = d.sub(pm2, one_nat);
        let big_p = d.of_nat(pp);
        let one_i = d.ione();

        // sigma' := fun i => sub (inverseIndex pp (succ i)) one.
        let sigma_prime = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let si = d.succ(i);
            let sigma_si = d.const_app(p.inverse_index, &[pp, si]);
            let body = d.sub(sigma_si, one_nat);
            d.lam_fv(i_fv, nat, body)
        };
        // G := fun i => ofNat (succ (succ i)).
        let big_g = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let si = d.succ(i);
            let ssi = d.succ(si);
            let body = d.of_nat(ssi);
            d.lam_fv(i_fv, nat, body)
        };

        let concl = {
            let pr = d.const_app(p.prod_range, &[big_g, pm3]);
            super::modeq::imodeq(d, big_p, pr, one_i)
        };
        let stmt = d.arrow(prime_ty, concl);

        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);

        let pos_big_p = nat_prime_pos(d, pp, prime_proof); // also Int.lt zero_i big_p, by defeq

        // maps_pf : MapsInto sigma_prime pm3.
        let maps_pf = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hi_fv = d.fresh_fvar();
            let hi_ty = d.lt(i, pm3);
            let hi = d.kernel().fvar(hi_fv);
            let bundle = sigma_prime_at(d, pp, prime_proof, i, hi);
            let with_hi = d.lam_fv(hi_fv, hi_ty, bundle.maps);
            d.lam_fv(i_fv, nat, with_hi)
        };

        // fpf_pf : ∀ i, Lt i pm3 → Not (Eq Nat (sigma_prime i) i).
        let fpf_pf = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hi_fv = d.fresh_fvar();
            let hi_ty = d.lt(i, pm3);
            let hi = d.kernel().fvar(hi_fv);
            let bundle = sigma_prime_at(d, pp, prime_proof, i, hi);
            let with_hi = d.lam_fv(hi_fv, hi_ty, bundle.fpf);
            d.lam_fv(i_fv, nat, with_hi)
        };

        // invol_pf : ∀ i, Lt i pm3 → Eq Nat (sigma_prime (sigma_prime i)) i.
        let invol_pf = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hi_fv = d.fresh_fvar();
            let hi_ty = d.lt(i, pm3);
            let hi = d.kernel().fvar(hi_fv);

            let bundle_i = sigma_prime_at(d, pp, prime_proof, i, hi);
            let j = bundle_i.val;
            let hj = bundle_i.maps;
            let bundle_j = sigma_prime_at(d, pp, prime_proof, j, hj);

            // bundle_j.k IS succ(j) IS succ(bundle_i.val), the same
            // construction bundle_i.succ_val_eq_sigma_k's LHS uses.
            let kj_eq_sigma_k = bundle_i.succ_val_eq_sigma_k; // Eq Nat bundle_j.k bundle_i.sigma_k
            let sigma_sigma_k = d.const_app(p.inverse_index, &[pp, bundle_i.sigma_k]);
            let sigma_kj_eq_sigma_sigma_k =
                d.congr(bundle_j.k, bundle_i.sigma_k, kj_eq_sigma_k, &|d, x| {
                    d.const_app(p.inverse_index, &[pp, x])
                }); // Eq Nat bundle_j.sigma_k sigma_sigma_k
            let sigma_kj_eq_k = d.trans(
                bundle_j.sigma_k,
                sigma_sigma_k,
                bundle_i.k,
                sigma_kj_eq_sigma_sigma_k,
                bundle_i.invol_k,
            ); // Eq Nat bundle_j.sigma_k bundle_i.k

            let succ_valj = d.succ(bundle_j.val);
            let succ_valj_eq_k = d.trans(
                succ_valj,
                bundle_j.sigma_k,
                bundle_i.k,
                bundle_j.succ_val_eq_sigma_k,
                sigma_kj_eq_k,
            ); // Eq Nat (succ bundle_j.val) bundle_i.k = Eq Nat (succ bundle_j.val) (succ i)

            let succ_inj_fn = d.lemma(p.nat.succ_injective, &[bundle_j.val, i]);
            let invol_i = d.apply(succ_inj_fn, &[succ_valj_eq_k]); // Eq Nat bundle_j.val i

            let with_hi = d.lam_fv(hi_fv, hi_ty, invol_i);
            d.lam_fv(i_fv, nat, with_hi)
        };

        // inj_pf : InjectiveOn sigma_prime pm3, generically from invol_pf.
        let inj_pf = injective_of_involutive_local(d, sigma_prime, invol_pf, pm3);

        // pairwise_pf : ∀ i, Lt i pm3 → ModEq big_p (mul (G i) (G (sigma_prime i))) one.
        let pairwise_pf = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hi_fv = d.fresh_fvar();
            let hi_ty = d.lt(i, pm3);
            let hi = d.kernel().fvar(hi_fv);

            let bundle = sigma_prime_at(d, pp, prime_proof, i, hi);
            let pairwise_raw =
                pairwise_modeq_general(d, pp, prime_proof, pm1, bundle.k, bundle.hk_lt_pm1);

            let sk_outer = d.succ(bundle.k);
            let fk = d.of_nat(sk_outer); // = G i, defeq
            let succ_sigma_k = d.succ(bundle.sigma_k);
            let f_sigma_k = d.of_nat(succ_sigma_k);
            let succ_val = d.succ(bundle.val);
            let succ_succ_val = d.succ(succ_val);
            let g_val = d.of_nat(succ_succ_val); // = G (sigma_prime i), defeq

            let g_val_eq_f_sigma_k = d.nat_eq_to_int(
                succ_val,
                bundle.sigma_k,
                bundle.succ_val_eq_sigma_k,
                &|d, x| {
                    let sx = d.succ(x);
                    d.of_nat(sx)
                },
            ); // Eq Int g_val f_sigma_k
            let f_sigma_k_eq_g_val = d.isymm(g_val, f_sigma_k, g_val_eq_f_sigma_k);

            let pairwise_i = d.int_eq_rewrite(
                f_sigma_k,
                g_val,
                f_sigma_k_eq_g_val,
                pairwise_raw,
                &|d, x| {
                    let lhs = d.imul(fk, x);
                    super::modeq::imodeq(d, big_p, lhs, one_i)
                },
            );

            let with_hi = d.lam_fv(hi_fv, hi_ty, pairwise_i);
            d.lam_fv(i_fv, nat, with_hi)
        };

        let body = d.const_app(
            p.prod_range_pairing_collapse,
            &[
                big_p,
                pos_big_p,
                pm3,
                big_g,
                sigma_prime,
                inj_pf,
                maps_pf,
                fpf_pf,
                invol_pf,
                pairwise_pf,
            ],
        );

        let proof = d.lam_fv(prime_fv, prime_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Int.wilson` — the assembly, landed 2026-08-24.
//
// `factorial(p-1) = prodRange F (p-1) = mul(prodRange F (p-2), F(p-2))`
// (`succ_pm2_eq_pm1` + `prodRange_succ`, unconditional). The two pieces:
//
// - `F(p-2) = ofNat(p-1) ≡ -1 [p]`, unconditional for every prime (the same
//   `Int.sub`-unfolding bridge `declare_inverse_index_fixed_point` builds as
//   `sub_eq_pm1`, composed with [`neg_one_modeq_p_minus_one`]).
// - `prodRange F (p-2) ≡ 1 [p]` — THIS is where `p = 2` needs its own
//   argument, and only here: relating `prodRange F (p-2)` to `prodRange F
//   (succ (p-3))` needs `p-2 = succ(p-3)`, which holds only when `p-2 > 0`,
//   i.e. `p ≥ 3`. Case split on `Nat.lt_or_eq_of_le` at `2 ≤ p` (`Lt 2 p ∨ Eq
//   Nat 2 p`, i.e. `p ≥ 3` or `p = 2`):
//   - `p ≥ 3`: `prodRange F (p-2) = prodRange F (succ (p-3)) = mul(F 0,
//     prodRange G (p-3))` (`Int.prodRange_shiftFront`), and `F 0 = one`
//     (delta-unfold) with `prodRange G (p-3) ≡ 1 [p]`
//     ([`declare_factorial_interior_modeq_one`]) gives `≡ mul(one,1) ≡ 1
//     [p]`.
//   - `p = 2`: `p-2 = 0` directly (rewriting the `p=2` hypothesis through
//     `pm2`'s own definition, a closed computation), so `prodRange F (p-2) =
//     prodRange F 0 = one` (`prodRange_zero`) — no need for
//     `factorial_interior_modeq_one` or the shift at all in this branch, the
//     interior is simply empty.
//
// Both branches conclude the same `ModEq (ofNat p) (prodRange F (p-2)) one`,
// so `Or.rec` closes the split into a single proof, which is then combined
// with the `F(p-2) ≡ -1 [p]` piece via `Int.ModEq.mul` and rewritten back
// through `factorial`'s own unfold.
// ============================================================================

/// `Eq Int (sub (ofNat pp) one) (ofNat pm1)`, for `pm1 := sub pp one_nat`,
/// given `1 ≤ pp`. The same `Int.sub`-unfolding bridge
/// [`declare_inverse_index_fixed_point`] builds inline as `sub_eq_pm1`
/// (`Int.sub` unfolds transparently to `add a (neg b)`, so `Nat.sub_add_cancel`
/// plus `Int.add_neg_cancel_right` closes it with no case split on the
/// symbolic magnitude), extracted here as its own function since
/// [`declare_wilson`] needs it standalone rather than as one step inside a
/// longer inline chain.
pub(super) fn ofnat_pm1_eq_sub_one(d: &mut IntDev<'_>, pp: ExprId, one_le_pp: ExprId) -> ExprId {
    let p = d.int();
    let one_nat = d.num(1);
    let one_i = d.ione();
    let neg_one = d.ineg(one_i);
    let big_p = d.of_nat(pp);
    let pm1 = d.sub(pp, one_nat);
    let ofnat_pm1 = d.of_nat(pm1);

    let succ_pm1 = d.succ(pm1);
    let cancel1 = d.lemma(p.nat.sub_add_cancel, &[one_nat, pp, one_le_pp]); // ~ Eq Nat succ_pm1 pp
    let key = d.nat_eq_to_int(succ_pm1, pp, cancel1, &|d, y| d.of_nat(y)); // Eq Int (ofNat succ_pm1) big_p

    let sum_pm1_one = d.iadd(ofnat_pm1, one_i);
    let cancel_right = d.const_app(p.add_neg_cancel_right, &[ofnat_pm1, one_i]); // Eq Int (sum_pm1_one + neg_one) ofnat_pm1
    let congr_key = d.icongr(sum_pm1_one, big_p, key, &|d, t| d.iadd(t, neg_one)); // Eq Int (sum_pm1_one+neg_one) (big_p+neg_one)
    let lhs_after = d.iadd(big_p, neg_one); // defeq `sub big_p one_i`
    let x_term = d.iadd(sum_pm1_one, neg_one);
    let congr_key_rev = d.isymm(x_term, lhs_after, congr_key); // Eq Int lhs_after x_term
    d.itrans(lhs_after, x_term, ofnat_pm1, congr_key_rev, cancel_right) // Eq Int lhs_after ofnat_pm1
}

/// `ModEq (ofNat pp) (ofNat pm1) (neg one)`, for `pm1 := sub pp one_nat`,
/// given `pos_big_p : Int.lt zero (ofNat pp)`. Composes
/// [`ofnat_pm1_eq_sub_one`] with [`neg_one_modeq_p_minus_one`].
fn ofnat_pm1_modeq_neg_one(
    d: &mut IntDev<'_>,
    pp: ExprId,
    one_le_pp: ExprId,
    pos_big_p: ExprId,
) -> ExprId {
    let p = d.int();
    let one_nat = d.num(1);
    let one_i = d.ione();
    let neg_one = d.ineg(one_i);
    let big_p = d.of_nat(pp);
    let pm1 = d.sub(pp, one_nat);
    let ofnat_pm1 = d.of_nat(pm1);
    let p_minus_one = d.isub(big_p, one_i);

    let sub_eq_pm1 = ofnat_pm1_eq_sub_one(d, pp, one_le_pp); // Eq Int p_minus_one ofnat_pm1 (nominally lhs_after)
    let base_modeq = neg_one_modeq_p_minus_one(d, big_p, pos_big_p); // ModEq big_p neg_one p_minus_one
    let rewritten = d.int_eq_rewrite(p_minus_one, ofnat_pm1, sub_eq_pm1, base_modeq, &|d, x| {
        super::modeq::imodeq(d, big_p, neg_one, x)
    }); // ModEq big_p neg_one ofnat_pm1
    d.const_app(p.mod_eq_symm, &[big_p, neg_one, ofnat_pm1, rewritten]) // ModEq big_p ofnat_pm1 neg_one
}

/// `ModEq (ofNat pp) (prodRange F pm2) one`, in the `p ≥ 3` branch (`hlt : Lt
/// two_nat pp`): `pm2 > 0` (derived from `hlt` by peeling two `succ`s off
/// `pp = succ(succ(pm2))`, itself `Nat.sub_add_cancel` at `(2, pp, two_le)`),
/// hence `pm2 = succ(pm3)`, so `prodRange_shiftFront` applies.
fn outer_collapse_ge3(
    d: &mut IntDev<'_>,
    pp: ExprId,
    prime_proof: ExprId,
    hlt: ExprId,
    interior_modeq: ExprId,
) -> ExprId {
    let p = d.int();
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let zero = d.zero();
    let pm2 = d.sub(pp, two_nat);
    let pm3 = d.sub(pm2, one_nat);
    let big_p = d.of_nat(pp);
    let one_i = d.ione();

    let (two_le_ty, clause_ty) = prime_parts(d, pp);
    let two_le = d.and_left(two_le_ty, clause_ty, prime_proof);
    let one_le_pp = nat_prime_pos(d, pp, prime_proof);
    let pos_big_p = one_le_pp;

    // pp = succ(succ(pm2)), via Nat.sub_add_cancel(2, pp, two_le).
    let succ_succ_pm2_eq_pp = d.lemma(p.nat.sub_add_cancel, &[two_nat, pp, two_le]); // ~ Eq Nat (succ(succ pm2)) pp
    let succ_pm2 = d.succ(pm2);
    let succ_succ_pm2 = d.succ(succ_pm2);
    let pp_eq_succ_succ_pm2 = d.symm(succ_succ_pm2, pp, succ_succ_pm2_eq_pp); // Eq Nat pp succ_succ_pm2

    // hlt : Lt two_nat pp = Le (succ two_nat) pp; rewrite pp -> succ_succ_pm2.
    let three_nat = d.succ(two_nat);
    let hlt_rewritten = d.nat_rewrite(pp, succ_succ_pm2, pp_eq_succ_succ_pm2, hlt, &|d, x| {
        d.le(three_nat, x)
    }); // Le three_nat succ_succ_pm2 = Le (succ two_nat)(succ succ_pm2)
    let peel1_fn = d.lemma(p.nat.le_of_succ_le_succ, &[two_nat, succ_pm2]);
    let step1 = d.apply(peel1_fn, &[hlt_rewritten]); // Le two_nat succ_pm2 = Le (succ one_nat)(succ pm2)
    let peel2_fn = d.lemma(p.nat.le_of_succ_le_succ, &[one_nat, pm2]);
    let pos_pm2 = d.apply(peel2_fn, &[step1]); // Le one_nat pm2

    // pm2 = succ(pm3).
    let succ_pm3_eq_pm2 = d.lemma(p.nat.sub_add_cancel, &[one_nat, pm2, pos_pm2]); // ~ Eq Nat (succ pm3) pm2
    let succ_pm3 = d.succ(pm3);
    let succ_pm3_eq_pm2_rev = d.symm(succ_pm3, pm2, succ_pm3_eq_pm2); // Eq Nat pm2 succ_pm3

    // F, G.
    let big_f = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let body = d.of_nat(sk);
        let nat = d.nat_ty();
        d.lam_fv(k_fv, nat, body)
    };
    let big_g = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let si = d.succ(i);
        let ssi = d.succ(si);
        let body = d.of_nat(ssi);
        let nat = d.nat_ty();
        d.lam_fv(i_fv, nat, body)
    };

    // prodRange F pm2 = prodRange F (succ pm3) = mul(F 0, prodRange G pm3).
    let pr_pm2 = d.const_app(p.prod_range, &[big_f, pm2]);
    let pr_succ_pm3 = d.const_app(p.prod_range, &[big_f, succ_pm3]);
    let pr_pm2_eq_pr_succ_pm3 = d.nat_eq_to_int(pm2, succ_pm3, succ_pm3_eq_pm2_rev, &|d, x| {
        d.const_app(p.prod_range, &[big_f, x])
    }); // Eq Int pr_pm2 pr_succ_pm3
    let shift_pf = d.const_app(p.prod_range_shift_front, &[big_f, pm3]); // Eq Int pr_succ_pm3 (mul (F 0)(prodRange G pm3)), G defeq the shifted lambda
    let f0 = d.apply(big_f, &[zero]);
    let pr_g_pm3 = d.const_app(p.prod_range, &[big_g, pm3]);
    let mul_f0_prg = d.imul(f0, pr_g_pm3);
    let pr_pm2_eq_mul = d.itrans(
        pr_pm2,
        pr_succ_pm3,
        mul_f0_prg,
        pr_pm2_eq_pr_succ_pm3,
        shift_pf,
    );

    // ModEq big_p (mul f0 pr_g_pm3)(mul f0 one), from interior_modeq scaled on the left.
    let scaled_modeq = d.const_app(
        p.mod_eq_mul_left,
        &[big_p, pr_g_pm3, one_i, f0, pos_big_p, interior_modeq],
    );
    let mul_f0_one = d.imul(f0, one_i);
    let mul_f0_one_eq_f0 = d.const_app(p.mul_one, &[f0]); // Eq Int mul_f0_one f0
    let scaled_modeq_2 =
        d.int_eq_rewrite(mul_f0_one, f0, mul_f0_one_eq_f0, scaled_modeq, &|d, x| {
            super::modeq::imodeq(d, big_p, mul_f0_prg, x)
        }); // ModEq big_p mul_f0_prg f0 (defeq one)

    let pr_pm2_eq_mul_rev = d.isymm(pr_pm2, mul_f0_prg, pr_pm2_eq_mul); // Eq Int mul_f0_prg pr_pm2
    d.int_eq_rewrite(
        mul_f0_prg,
        pr_pm2,
        pr_pm2_eq_mul_rev,
        scaled_modeq_2,
        &|d, x| super::modeq::imodeq(d, big_p, x, one_i),
    ) // ModEq big_p pr_pm2 one
}

/// `ModEq (ofNat pp) (prodRange F pm2) one`, in the `p = 2` branch (`heq : Eq
/// Nat two_nat pp`): `pm2 = 0` directly, so `prodRange F pm2 = prodRange F 0
/// = one` (`prodRange_zero`) — no reindex needed at all.
fn outer_collapse_eq2(d: &mut IntDev<'_>, pp: ExprId, heq: ExprId) -> ExprId {
    let p = d.int();
    let two_nat = d.num(2);
    let zero = d.zero();
    let pm2 = d.sub(pp, two_nat);
    let big_p = d.of_nat(pp);
    let one_i = d.ione();

    let concrete_zero = d.refl(zero); // Eq Nat zero zero, retyped below
    let pm2_eq_zero = d.nat_rewrite(two_nat, pp, heq, concrete_zero, &|d, x| {
        let s = d.sub(x, two_nat);
        d.eq(s, zero)
    }); // Eq Nat pm2 zero (defeq: sub two_nat two_nat ~ zero)

    let big_f = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let body = d.of_nat(sk);
        let nat = d.nat_ty();
        d.lam_fv(k_fv, nat, body)
    };
    let pr_pm2 = d.const_app(p.prod_range, &[big_f, pm2]);
    let pr_zero = d.const_app(p.prod_range, &[big_f, zero]);
    let pr_pm2_eq_pr_zero = d.nat_eq_to_int(pm2, zero, pm2_eq_zero, &|d, x| {
        d.const_app(p.prod_range, &[big_f, x])
    }); // Eq Int pr_pm2 pr_zero
    let pr_zero_eq_one = d.irefl(one_i); // Eq Int pr_zero one, defeq (prodRange_zero)
    let pr_pm2_eq_one = d.itrans(pr_pm2, pr_zero, one_i, pr_pm2_eq_pr_zero, pr_zero_eq_one);

    let refl_modeq_one = d.const_app(p.mod_eq_refl, &[big_p, one_i]); // ModEq big_p one one
    let pr_pm2_eq_one_rev = d.isymm(pr_pm2, one_i, pr_pm2_eq_one); // Eq Int one pr_pm2
    d.int_eq_rewrite(one_i, pr_pm2, pr_pm2_eq_one_rev, refl_modeq_one, &|d, x| {
        super::modeq::imodeq(d, big_p, x, one_i)
    }) // ModEq big_p pr_pm2 one
}

/// `Int.wilson : ∀ p, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) →
///   ModEq (ofNat p) (factorial (p-1)) (neg one)`
///
/// See this module's doc section above for the route.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_wilson(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.wilson, 1, &|d, v| {
        let pp = v[0];
        let prime_ty = prime_condition(d, pp);

        let one_nat = d.num(1);
        let two_nat = d.num(2);
        let pm1 = d.sub(pp, one_nat);
        let pm2 = d.sub(pp, two_nat);
        let big_p = d.of_nat(pp);
        let one_i = d.ione();
        let neg_one = d.ineg(one_i);

        let factorial_pm1 = d.const_app(p.factorial, &[pm1]);
        let concl = super::modeq::imodeq(d, big_p, factorial_pm1, neg_one);
        let stmt = d.arrow(prime_ty, concl);

        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);

        let (two_le_ty, clause_ty) = prime_parts(d, pp);
        let two_le = d.and_left(two_le_ty, clause_ty, prime_proof);
        let one_le_pp = nat_prime_pos(d, pp, prime_proof);
        let pos_big_p = one_le_pp;

        // F(pm2) ≡ -1 [p], unconditional.
        let big_f = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sk = d.succ(k);
            let body = d.of_nat(sk);
            let nat = d.nat_ty();
            d.lam_fv(k_fv, nat, body)
        };
        let f_pm2 = d.apply(big_f, &[pm2]); // = ofNat(succ pm2)
        let succ_pm2_eq_pm1_pf = succ_pm2_eq_pm1(d, pp, prime_proof); // Eq Nat succ_pm2 pm1
        let succ_pm2 = d.succ(pm2);
        let ofnat_pm1_modeq_neg = ofnat_pm1_modeq_neg_one(d, pp, one_le_pp, pos_big_p); // ModEq big_p (ofNat pm1) neg_one
        let ofnat_pm1 = d.of_nat(pm1);
        let f_pm2_eq_ofnat_pm1 =
            d.nat_eq_to_int(succ_pm2, pm1, succ_pm2_eq_pm1_pf, &|d, y| d.of_nat(y)); // Eq Int f_pm2 ofnat_pm1
        let ofnat_pm1_eq_f_pm2 = d.isymm(f_pm2, ofnat_pm1, f_pm2_eq_ofnat_pm1); // Eq Int ofnat_pm1 f_pm2
        let f_pm2_modeq_neg = d.int_eq_rewrite(
            ofnat_pm1,
            f_pm2,
            ofnat_pm1_eq_f_pm2,
            ofnat_pm1_modeq_neg,
            &|d, x| super::modeq::imodeq(d, big_p, x, neg_one),
        ); // ModEq big_p f_pm2 neg_one

        // prodRange F pm2 ≡ 1 [p], via the p ≥ 3 / p = 2 case split.
        let disj = d.lemma(p.nat.lt_or_eq_of_le, &[two_nat, pp, two_le]); // Or (Lt two_nat pp)(Eq Nat two_nat pp)
        let lt_ty = d.lt(two_nat, pp);
        let eq_ty = d.eq(two_nat, pp);
        let pr_pm2 = d.const_app(p.prod_range, &[big_f, pm2]);
        let outer_target = super::modeq::imodeq(d, big_p, pr_pm2, one_i);
        let outer_collapse = d.or_elim(
            lt_ty,
            eq_ty,
            outer_target,
            disj,
            &|d, hlt| {
                let interior_modeq =
                    d.const_app(p.factorial_interior_modeq_one, &[pp, prime_proof]);
                outer_collapse_ge3(d, pp, prime_proof, hlt, interior_modeq)
            },
            &|d, heq| outer_collapse_eq2(d, pp, heq),
        );

        // Combine: ModEq big_p (mul pr_pm2 f_pm2)(mul one neg_one), then mul_one.
        let pr_mul = d.const_app(
            p.mod_eq_mul,
            &[
                big_p,
                pr_pm2,
                one_i,
                f_pm2,
                neg_one,
                pos_big_p,
                outer_collapse,
                f_pm2_modeq_neg,
            ],
        ); // ModEq big_p (mul pr_pm2 f_pm2)(mul one neg_one)
        let mul_one_negone = d.imul(one_i, neg_one);
        let mul_one_negone_eq_negone = d.const_app(p.one_mul, &[neg_one]); // Eq Int mul_one_negone neg_one
        let mul_pm2_fpm2 = d.imul(pr_pm2, f_pm2);
        let pr_mul_2 = d.int_eq_rewrite(
            mul_one_negone,
            neg_one,
            mul_one_negone_eq_negone,
            pr_mul,
            &|d, x| super::modeq::imodeq(d, big_p, mul_pm2_fpm2, x),
        ); // ModEq big_p mul_pm2_fpm2 neg_one

        // factorial(pm1) = factorial(succ pm2), defeq mul(prodRange F pm2, F pm2).
        let succ_pm2_eq_pm1_pf2 = succ_pm2_eq_pm1(d, pp, prime_proof);
        let pm1_eq_succ_pm2 = d.symm(succ_pm2, pm1, succ_pm2_eq_pm1_pf2); // Eq Nat pm1 succ_pm2
        let factorial_succ_pm2 = d.const_app(p.factorial, &[succ_pm2]);
        let factorial_eq = d.nat_eq_to_int(pm1, succ_pm2, pm1_eq_succ_pm2, &|d, x| {
            d.const_app(p.factorial, &[x])
        }); // Eq Int factorial_pm1 factorial_succ_pm2
        let factorial_eq_rev = d.isymm(factorial_pm1, factorial_succ_pm2, factorial_eq); // Eq Int factorial_succ_pm2 factorial_pm1

        let body = d.int_eq_rewrite(
            factorial_succ_pm2,
            factorial_pm1,
            factorial_eq_rev,
            pr_mul_2,
            &|d, x| super::modeq::imodeq(d, big_p, x, neg_one),
        ); // ModEq big_p factorial_pm1 neg_one

        let proof = d.lam_fv(prime_fv, prime_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Int.wilson_converse` — Wilson's theorem run backwards, landed 2026-08-24.
//
// The easy direction: if `dd ∣ n` with `1 ≤ dd < n`, then `dd ≤ n-1`, so
// `dd ∣ (n-1)!` (`Int.dvd_factorial_of_le`, below — built fresh rather than
// transported from `Nat.dvd_factorial_of_le`, since `Int.factorial n` and
// `ofNat (Nat.factorial n)` are not definitionally equal: `Int.factorial`
// unfolds via `Int.prodRange`, not `Nat.factorial`'s own recursion). Combined
// with `n ∣ (-1 - (n-1)!)` (from the hypothesis `(n-1)! ≡ -1 [n]` via
// `Int.modEq_iff_dvd`, composed with `dd ∣ n` via `Int.dvd_trans`),
// `Int.dvd_add` gives `dd ∣ ((n-1)! + (-1 - (n-1)!))`, and
// `add_sub_self_cancel` (below) rewrites the sum to exactly `-1`, so
// `dd ∣ -1`, and `Nat.eq_one_of_dvd_one` (via `natAbs`) forces `dd = 1`.
//
// Unlike the forward direction, this needs no permutation, no pairing, no
// modular inverse, and — because the target is the CONJUNCTIVE `Prime n`
// (`2 ≤ n ∧ ∀ d, d ∣ n → d = 1 ∨ d = n)`, not a negation — no excluded
// middle: `Nat.lt_or_eq_of_le` supplies a genuine constructive disjunction
// on `dd ≤ n`, and every other step is divisibility arithmetic.
// ============================================================================

/// `Eq Int (add a (sub b a)) b` — `a + (b - a) = b`. `Int.sub b a` unfolds
/// transparently to `add b (neg a)` (`Int.sub` is `add a (neg b)` by
/// definition, so no case split on either argument's magnitude is needed —
/// the same transparency [`declare_wilson`]'s own `ofnat_pm1_eq_sub_one`
/// leans on), so the chain runs entirely over `Int.add`/`Int.neg`:
/// reassociate `a + (b + (-a))` to `(a+b) + (-a)`, commute the inner sum to
/// `(b+a) + (-a)`, reassociate to `b + (a + (-a))`, collapse `a + (-a)` via
/// `add_neg`, and close with `add_zero`.
fn add_sub_self_cancel(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let p = d.int();
    let sub_ba = d.isub(b, a);
    let start = d.iadd(a, sub_ba); // a + (b - a), the shape `Int.dvd_add` hands back
    let neg_a = d.ineg(a);
    let b_plus_neg_a = d.iadd(b, neg_a);
    let unfolded = d.iadd(a, b_plus_neg_a); // a + (b + (-a)), defeq to `start`
    let start_eq_unfolded = d.irefl(start); // typed as `Eq Int start unfolded`, via defeq

    let ab = d.iadd(a, b);
    let step1_rhs = d.iadd(ab, neg_a); // (a+b) + (-a)
    let assoc1 = d.const_app(p.add_assoc, &[a, b, neg_a]); // Eq Int step1_rhs unfolded
    let step1_proof = d.isymm(step1_rhs, unfolded, assoc1); // Eq Int unfolded step1_rhs

    let ba = d.iadd(b, a);
    let comm_ab = d.const_app(p.add_comm, &[a, b]); // Eq Int ab ba
    let step2_rhs = d.iadd(ba, neg_a); // (b+a) + (-a)
    let step2_proof = d.icongr(ab, ba, comm_ab, &|d, t| d.iadd(t, neg_a)); // Eq Int step1_rhs step2_rhs

    let a_neg_a = d.iadd(a, neg_a); // a + (-a)
    let step3_rhs = d.iadd(b, a_neg_a); // b + (a + (-a))
    let assoc3 = d.const_app(p.add_assoc, &[b, a, neg_a]); // Eq Int step2_rhs step3_rhs

    let zero = d.izero();
    let add_neg_a = d.const_app(p.add_neg, &[a]); // Eq Int a_neg_a zero
    let step4_rhs = d.iadd(b, zero); // b + 0
    let step4_proof = d.icongr(a_neg_a, zero, add_neg_a, &|d, t| d.iadd(b, t)); // Eq Int step3_rhs step4_rhs

    let add_zero_b = d.const_app(p.add_zero, &[b]); // Eq Int step4_rhs b

    let (_, proof) = d.ichain(
        start,
        &[
            (unfolded, start_eq_unfolded),
            (step1_rhs, step1_proof),
            (step2_rhs, step2_proof),
            (step3_rhs, assoc3),
            (step4_rhs, step4_proof),
            (b, add_zero_b),
        ],
    );
    proof
}

/// `Int.dvd_factorial_of_le : ∀ (dd n : Nat), Le 1 dd → Le dd n →
///   dvd (ofNat dd) (factorial n)`.
///
/// The workhorse [`declare_wilson_converse`] needs: a positive `dd ≤ n`
/// divides `n!`, transported to `ℤ`. Mirrors `Nat.dvd_factorial_of_le`
/// (`nat_prelude/divisibility.rs`) bit for bit, built fresh here rather than
/// transported through it — see this module's doc section above for why no
/// cheap defeq bridge between `Int.factorial n` and `ofNat (Nat.factorial n)`
/// exists.
///
/// Induction on `n`:
///   zero    `1 ≤ dd ≤ 0` chains (`Nat.le_trans`) to `1 ≤ 0`, refuted by
///           `Nat.not_succ_le_zero` (`Int.absurd`, i.e. `False.rec`, supplies
///           the goal).
///   succ j  `Nat.lt_or_eq_of_le` splits `dd ≤ succ j` into `dd < succ j` or
///           `dd = succ j`. `factorial (succ j) ≡ mul (factorial j)
///           (ofNat (succ j))` holds DEFINITIONALLY (the same unfold
///           `Int.factorial_succ`'s own `Eq.refl` proof relies on), so
///           neither branch rewrites the goal to reach it:
///             * `dd < succ j` is `succ dd ≤ succ j`, so
///               `le_of_succ_le_succ` gives `dd ≤ j`; the IH gives
///               `dvd (ofNat dd) (factorial j)`, and `Int.dvd_trans` against
///               `Int.dvd_mul_right (factorial j) (ofNat (succ j))` extends
///               it across the new factor;
///             * `dd = succ j` uses `Int.dvd_mul_left (ofNat (succ j))
///               (factorial j) : dvd (ofNat (succ j)) (mul (factorial j)
///               (ofNat (succ j)))` directly, then transports `ofNat
///               (succ j)` back to `ofNat dd` along the branch equation.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_dvd_factorial_of_le(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.dvd_factorial_of_le, 2, &|d, values| {
        let (divisor, bound) = (values[0], values[1]);
        let zero = d.zero();
        let unit = d.succ(zero);
        let positive_ty = d.le(unit, divisor);
        let order_ty = d.le(divisor, bound);
        let conclusion = {
            let of_divisor = d.of_nat(divisor);
            let factorial = d.const_app(p.factorial, &[bound]);
            super::dvd::idvd(d, of_divisor, factorial)
        };
        let stmt = {
            let inner = d.arrow(order_ty, conclusion);
            d.arrow(positive_ty, inner)
        };

        let positive_fv = d.fresh_fvar();
        let positive = d.kernel().fvar(positive_fv);

        let claim = |d: &mut IntDev<'_>, x: ExprId| {
            let hypothesis = d.le(divisor, x);
            let of_divisor = d.of_nat(divisor);
            let factorial = d.const_app(p.factorial, &[x]);
            let target = super::dvd::idvd(d, of_divisor, factorial);
            d.arrow(hypothesis, target)
        };

        let at_zero = |d: &mut IntDev<'_>| {
            let zero = d.zero();
            let hypothesis_ty = d.le(divisor, zero);
            let goal = {
                let of_divisor = d.of_nat(divisor);
                let factorial = d.const_app(p.factorial, &[zero]);
                super::dvd::idvd(d, of_divisor, factorial)
            };
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let unit = d.succ(zero);
            let one_le_zero = d.lemma(p.nat.le_trans, &[unit, divisor, zero, positive, h]);
            let contradiction = d.lemma(p.nat.not_succ_le_zero, &[zero, one_le_zero]);
            let body = d.absurd(goal, contradiction);
            d.lam_fv(h_fv, hypothesis_ty, body)
        };

        let at_succ = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| {
            let successor = d.succ(j);
            let hypothesis_ty = d.le(divisor, successor);
            let of_divisor = d.of_nat(divisor);
            let target = {
                let factorial = d.const_app(p.factorial, &[successor]);
                super::dvd::idvd(d, of_divisor, factorial)
            };
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let strict_ty = d.lt(divisor, successor);
            let equal_ty = d.eq(divisor, successor);
            let split = d.lemma(p.nat.lt_or_eq_of_le, &[divisor, successor, h]);

            let body = d.or_elim(
                strict_ty,
                equal_ty,
                target,
                split,
                &|d, hstrict| {
                    // `dd < succ j` unfolds to `succ dd ≤ succ j`, so the bound drops to `j`.
                    let smaller = d.lemma(p.nat.le_of_succ_le_succ, &[divisor, j, hstrict]);
                    let inherited = d.apply(ih, &[smaller]); // dvd of_divisor (factorial j)
                    let prior = d.const_app(p.factorial, &[j]);
                    let of_succ = d.of_nat(successor);
                    // `factorial j * succ j` IS `factorial (succ j)` definitionally.
                    let step = d.const_app(p.dvd_mul_right, &[prior, of_succ]); // dvd prior (prior*of_succ)
                    let prod = d.imul(prior, of_succ);
                    d.const_app(p.dvd_trans, &[of_divisor, prior, prod, inherited, step])
                },
                &|d, hequal| {
                    // `dd = succ j`: the last factor of `factorial (succ j)` is the divisor.
                    let prior = d.const_app(p.factorial, &[j]);
                    let of_succ = d.of_nat(successor);
                    let prod = d.imul(prior, of_succ);
                    let canonical = d.const_app(p.dvd_mul_left, &[of_succ, prior]); // dvd of_succ prod
                    // `hequal : dd = succ j`, and the transport replaces `succ j` by
                    // `dd`, so it needs the equation the OTHER way round.
                    let reverse = d.symm(divisor, successor, hequal); // Eq Nat successor divisor
                    let of_eq = d.nat_eq_to_int(successor, divisor, reverse, &|d, y| d.of_nat(y)); // Eq Int of_succ of_divisor
                    d.int_eq_rewrite(of_succ, of_divisor, of_eq, canonical, &|d, x| {
                        super::dvd::idvd(d, x, prod)
                    })
                },
            );
            d.lam_fv(h_fv, hypothesis_ty, body)
        };

        let selected = d.induct(&claim, &at_zero, &at_succ, bound);
        let proof = d.lam_fv(positive_fv, positive_ty, selected);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.wilson_converse : ∀ n, Le 2 n →
///   ModEq (ofNat n) (factorial (n-1)) (neg one) →
///   (2 ≤ n ∧ ∀ d, d ∣ n → d = 1 ∨ d = n)` — **the converse of Wilson's
/// theorem**, turning it into a characterization of primality: `n ≥ 2` and
/// `(n-1)! ≡ -1 [n]` together force `n` prime. Proved DIRECTLY in the
/// conjunctive `Prime n` form (not a contrapositive) — see this module's doc
/// section above for the route and why no excluded middle is needed.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_wilson_converse(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.wilson_converse, 1, &|d, v| {
        let nn = v[0];
        let two_nat = d.num(2);
        let one_nat = d.num(1);
        let two_le_ty = d.le(two_nat, nn);
        let nm1 = d.sub(nn, one_nat);
        let big_n = d.of_nat(nn);
        let one_i = d.ione();
        let neg_one = d.ineg(one_i);
        let factorial_nm1 = d.const_app(p.factorial, &[nm1]);
        let modeq_ty = super::modeq::imodeq(d, big_n, factorial_nm1, neg_one);
        let prime_ty = prime_condition(d, nn);
        let stmt = {
            let inner = d.arrow(modeq_ty, prime_ty);
            d.arrow(two_le_ty, inner)
        };

        let two_le_fv = d.fresh_fvar();
        let two_le = d.kernel().fvar(two_le_fv);
        let modeq_fv = d.fresh_fvar();
        let hmodeq = d.kernel().fvar(modeq_fv);

        // 1 ≤ nn, from 2 ≤ nn.
        let one_le_two = d.lemma(p.nat.le_succ, &[one_nat]);
        let one_le_nn = d.lemma(p.nat.le_trans, &[one_nat, two_nat, nn, one_le_two, two_le]);
        // `Int.lt zero big_n` reduces structurally to `Nat.lt zero nn` = `Nat.le 1 nn`
        // on two `ofNat`-headed arguments (`int_prelude/defs.rs`'s four-case table),
        // so the SAME term serves both roles — the same trick `declare_wilson`'s own
        // `pos_big_p := one_le_pp` relies on.
        let pos_big_n = one_le_nn;

        let (two_le_out, clause_ty) = prime_parts(d, nn);

        let clause_proof = {
            let dvar_fv = d.fresh_fvar();
            let dvar = d.kernel().fvar(dvar_fv);
            let hdvd_ty = d.dvd(dvar, nn);
            let is_one = d.eq(dvar, one_nat);
            let is_whole = d.eq(dvar, nn);
            let target = d.or(is_one, is_whole);

            let hdvd_fv = d.fresh_fvar();
            let hdvd = d.kernel().fvar(hdvd_fv);

            let le_d_nn = d.lemma(p.nat.le_of_dvd, &[dvar, nn, one_le_nn, hdvd]);
            let split = d.lemma(p.nat.lt_or_eq_of_le, &[dvar, nn, le_d_nn]);
            let lt_ty = d.lt(dvar, nn);
            let eq_ty = d.eq(dvar, nn);

            let body = d.or_elim(
                lt_ty,
                eq_ty,
                target,
                split,
                &|d, hlt| {
                    // `dd < nn`: derive `dd = 1`.
                    let one_le_d = d.lemma(p.nat.one_le_of_dvd_pos, &[dvar, nn, one_le_nn, hdvd]);

                    // nn = succ(nn-1), so `dd < nn` peels down to `dd ≤ nn-1`.
                    let succ_nm1_eq_nn = d.lemma(p.nat.sub_add_cancel, &[one_nat, nn, one_le_nn]);
                    let succ_nm1 = d.succ(nm1);
                    let nn_eq_succ_nm1 = d.symm(succ_nm1, nn, succ_nm1_eq_nn);
                    let succ_dvar = d.succ(dvar);
                    let hlt_rewritten =
                        d.nat_rewrite(nn, succ_nm1, nn_eq_succ_nm1, hlt, &|d, x| {
                            d.le(succ_dvar, x)
                        });
                    let d_le_nm1 = d.lemma(p.nat.le_of_succ_le_succ, &[dvar, nm1, hlt_rewritten]);

                    // dd ∣ (nn-1)!
                    let dvd_d_fact =
                        d.lemma(p.dvd_factorial_of_le, &[dvar, nm1, one_le_d, d_le_nm1]);

                    // dd ∣ nn, transported to ℤ.
                    let of_dvar = d.of_nat(dvar);
                    let dvd_d_n = d.const_app(p.dvd_of_nat_abs_dvd, &[of_dvar, big_n, hdvd]);

                    // nn ∣ (-1 - (nn-1)!), from the ModEq hypothesis.
                    let sub_ba = d.isub(neg_one, factorial_nm1);
                    let dvd_ty2 = super::dvd::idvd(d, big_n, sub_ba);
                    let iff_ty = d.const_app(
                        p.mod_eq_iff_dvd,
                        &[big_n, factorial_nm1, neg_one, pos_big_n],
                    );
                    let mp = d.const_app(p.logic.iff_mp, &[modeq_ty, dvd_ty2, iff_ty]);
                    let dvd_n_diff = d.apply(mp, &[hmodeq]);

                    // dd ∣ (-1 - (nn-1)!), by transitivity through `dd ∣ nn`.
                    let dvd_d_diff =
                        d.const_app(p.dvd_trans, &[of_dvar, big_n, sub_ba, dvd_d_n, dvd_n_diff]);

                    // dd ∣ ((nn-1)! + (-1 - (nn-1)!)), by `Int.dvd_add`.
                    let dvd_sum = d.const_app(
                        p.dvd_add,
                        &[of_dvar, factorial_nm1, sub_ba, dvd_d_fact, dvd_d_diff],
                    );

                    // The sum collapses to exactly `-1`, so `dd ∣ -1`.
                    let sum_term = d.iadd(factorial_nm1, sub_ba);
                    let identity = add_sub_self_cancel(d, factorial_nm1, neg_one);
                    let dvd_d_negone =
                        d.int_eq_rewrite(sum_term, neg_one, identity, dvd_sum, &|d, x| {
                            super::dvd::idvd(d, of_dvar, x)
                        });

                    // dd ∣ -1  =>  dd ∣ 1 (Nat, via natAbs)  =>  dd = 1.
                    let nat_dvd_one = d.const_app(
                        p.nat_abs_dvd_nat_abs_of_dvd,
                        &[of_dvar, neg_one, dvd_d_negone],
                    );
                    let d_eq_one = d.lemma(p.nat.eq_one_of_dvd_one, &[dvar, nat_dvd_one]);

                    d.or_inl(is_one, is_whole, d_eq_one)
                },
                &|d, heq| d.or_inr(is_one, is_whole, heq),
            );

            let inner_lam = d.lam_fv(hdvd_fv, hdvd_ty, body);
            let nat_ty = d.nat_ty();
            d.lam_fv(dvar_fv, nat_ty, inner_lam)
        };

        let and_proof = d.const_app(
            p.logic.and_intro,
            &[two_le_out, clause_ty, two_le, clause_proof],
        );
        let with_modeq = d.lam_fv(modeq_fv, modeq_ty, and_proof);
        let proof = d.lam_fv(two_le_fv, two_le_ty, with_modeq);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.wilson_iff : ∀ n, Le 2 n →
///   ((2 ≤ n ∧ ∀ d, d ∣ n → d = 1 ∨ d = n) ↔
///     ModEq (ofNat n) (factorial (n-1)) (neg one))` — Wilson's theorem AND
/// its converse combined: for `n ≥ 2`, primality is EQUIVALENT to
/// `(n-1)! ≡ -1 [n]`. `Iff.intro` of [`declare_wilson`] (mp) and
/// [`declare_wilson_converse`] (mpr).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_wilson_iff(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.wilson_iff, 1, &|d, v| {
        let nn = v[0];
        let two_nat = d.num(2);
        let one_nat = d.num(1);
        let two_le_ty = d.le(two_nat, nn);
        let nm1 = d.sub(nn, one_nat);
        let big_n = d.of_nat(nn);
        let one_i = d.ione();
        let neg_one = d.ineg(one_i);
        let factorial_nm1 = d.const_app(p.factorial, &[nm1]);
        let modeq_ty = super::modeq::imodeq(d, big_n, factorial_nm1, neg_one);
        let prime_ty = prime_condition(d, nn);
        let iff_ty = {
            let name = p.logic.iff;
            d.const_app(name, &[prime_ty, modeq_ty])
        };
        let stmt = d.arrow(two_le_ty, iff_ty);

        let two_le_fv = d.fresh_fvar();
        let two_le = d.kernel().fvar(two_le_fv);

        let mp = {
            let hp_fv = d.fresh_fvar();
            let hp = d.kernel().fvar(hp_fv);
            let body = d.const_app(p.wilson, &[nn, hp]);
            d.lam_fv(hp_fv, prime_ty, body)
        };
        let mpr = {
            let hm_fv = d.fresh_fvar();
            let hm = d.kernel().fvar(hm_fv);
            let body = d.const_app(p.wilson_converse, &[nn, two_le, hm]);
            d.lam_fv(hm_fv, modeq_ty, body)
        };
        let iff_proof = d.const_app(p.logic.iff_intro, &[prime_ty, modeq_ty, mp, mpr]);
        let proof = d.lam_fv(two_le_fv, two_le_ty, iff_proof);
        (stmt, proof)
    })?;
    Ok(())
}
